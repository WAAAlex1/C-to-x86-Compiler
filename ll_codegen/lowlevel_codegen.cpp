// Copyright (c) 2021-2024, David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.

#include <cassert>
#include <map>
#include "node.h"
#include "instruction.h"
#include "operand.h"
#include "local_storage_allocation.h"
#include "highlevel.h"
#include "lowlevel.h"
#include "highlevel_formatter.h"
#include "exceptions.h"
#include "lowlevel_codegen.h"

// This map has some "obvious" translations of high-level opcodes to
// low-level opcodes.
const std::map<HighLevelOpcode, LowLevelOpcode> HL_TO_LL = {
  { HINS_nop, MINS_NOP},
  { HINS_add_b, MINS_ADDB },
  { HINS_add_w, MINS_ADDW },
  { HINS_add_l, MINS_ADDL },
  { HINS_add_q, MINS_ADDQ },
  { HINS_sub_b, MINS_SUBB },
  { HINS_sub_w, MINS_SUBW },
  { HINS_sub_l, MINS_SUBL },
  { HINS_sub_q, MINS_SUBQ },
  { HINS_mul_l, MINS_IMULL },
  { HINS_mul_q, MINS_IMULQ },
  { HINS_mov_b, MINS_MOVB },
  { HINS_mov_w, MINS_MOVW },
  { HINS_mov_l, MINS_MOVL },
  { HINS_mov_q, MINS_MOVQ },
  { HINS_sconv_bw, MINS_MOVSBW },
  { HINS_sconv_bl, MINS_MOVSBL },
  { HINS_sconv_bq, MINS_MOVSBQ },
  { HINS_sconv_wl, MINS_MOVSWL },
  { HINS_sconv_wq, MINS_MOVSWQ },
  { HINS_sconv_lq, MINS_MOVSLQ },
  { HINS_uconv_bw, MINS_MOVZBW },
  { HINS_uconv_bl, MINS_MOVZBL },
  { HINS_uconv_bq, MINS_MOVZBQ },
  { HINS_uconv_wl, MINS_MOVZWL },
  { HINS_uconv_wq, MINS_MOVZWQ },
  { HINS_uconv_lq, MINS_MOVZLQ },
  { HINS_ret, MINS_RET },
  { HINS_jmp, MINS_JMP },
  { HINS_call, MINS_CALL },

  // For comparisons, it is expected that the code generator will first
  // generate a cmpb/cmpw/cmpl/cmpq instruction to compare the operands,
  // and then generate a setXX instruction to put the result of the
  // comparison into the destination operand. These entries indicate
  // the apprpropriate setXX instruction to use.
  { HINS_cmplt_b, MINS_SETL },
  { HINS_cmplt_w, MINS_SETL },
  { HINS_cmplt_l, MINS_SETL },
  { HINS_cmplt_q, MINS_SETL },
  { HINS_cmplte_b, MINS_SETLE },
  { HINS_cmplte_w, MINS_SETLE },
  { HINS_cmplte_l, MINS_SETLE },
  { HINS_cmplte_q, MINS_SETLE },
  { HINS_cmpgt_b, MINS_SETG },
  { HINS_cmpgt_w, MINS_SETG },
  { HINS_cmpgt_l, MINS_SETG },
  { HINS_cmpgt_q, MINS_SETG },
  { HINS_cmpgte_b, MINS_SETGE },
  { HINS_cmpgte_w, MINS_SETGE },
  { HINS_cmpgte_l, MINS_SETGE },
  { HINS_cmpgte_q, MINS_SETGE },
  { HINS_cmpeq_b, MINS_SETE },
  { HINS_cmpeq_w, MINS_SETE },
  { HINS_cmpeq_l, MINS_SETE },
  { HINS_cmpeq_q, MINS_SETE },
  { HINS_cmpneq_b, MINS_SETNE },
  { HINS_cmpneq_w, MINS_SETNE },
  { HINS_cmpneq_l, MINS_SETNE },
  { HINS_cmpneq_q, MINS_SETNE },
};

LowLevelCodeGen::LowLevelCodeGen(const Options &options)
  : m_options(options)
  , m_total_memory_storage(0)
  , m_local_storage(0)
  , m_register_storage(0){
}

LowLevelCodeGen::~LowLevelCodeGen() {
}

void LowLevelCodeGen::generate(std::shared_ptr<Function> function) {
  // Make the Function object available to member functions
  m_function = function;

  // The translation is done in the translate_hl_to_ll() member function
  std::shared_ptr<InstructionSequence> ll_iseq = translate_hl_to_ll(function->get_hl_iseq());
  m_function->set_ll_iseq(ll_iseq);
}

std::shared_ptr<InstructionSequence> LowLevelCodeGen::translate_hl_to_ll(std::shared_ptr<InstructionSequence> hl_iseq) {
  std::shared_ptr<InstructionSequence> ll_iseq(new InstructionSequence());

  // The high-level InstructionSequence will have a pointer to the Node
  // representing the function definition. Useful information could be stored
  // there (for example, about the amount of memory needed for local storage,
  // maximum number of virtual registers used, etc.)
  Node *funcdef_ast = m_function->get_funcdef_ast();
  assert(funcdef_ast != nullptr);

  // Determine the total number of bytes of memory storage
  // that the function needs. This should include both variables that
  // *must* have storage allocated in memory (e.g., arrays), and also
  // any additional memory that is needed for virtual registers,
  // spilled machine registers, etc.
  printf("/* ---------------------------%s---------------------------- */\n",m_function->get_name().c_str());
  m_local_storage  = m_function->get_total_storage();
  printf("/*FUNCTION %s USES %d BYTES OF MEMORY FOR STRUCTURES*/\n",m_function->get_name().c_str(), m_local_storage);
  if ((m_local_storage) % 8 != 0) m_local_storage += (8 - (m_local_storage % 8));
  m_register_storage = m_function->get_num_loc_regs()*8;

  //UNCOMMENT FOR OPTIMIZED VERSION
  //m_register_storage = m_function->get_vregAlloc()->get_total_register_storage();

  printf("/*FUNCTION %s USES %d BYTES OF MEMORY FOR REGISTERS*/\n",m_function->get_name().c_str(), m_register_storage);
  auto spilled_storage = m_function->get_total_spilled_storage();
  printf("/*FUNCTION %s USES %d BYTES OF MEMORY FOR SPILLS*/\n",m_function->get_name().c_str(),spilled_storage);

  m_total_memory_storage = m_local_storage + m_register_storage + spilled_storage;

  printf("/*FUNCTION %s: PLACES MEMORY VARIABLES AT OFFSET %d FROM %srbp*/\n",m_function->get_name().c_str(),-m_local_storage, "%");
  printf("/*FUNCTION %s: PLACES REGISTERS AT OFFSET %d FROM %srbp*/\n",m_function->get_name().c_str(), -(m_total_memory_storage-spilled_storage), "%");
  printf("/*FUNCTION %s: PLACES SPILLS AT OFFSET %d FROM %srbp*/\n",m_function->get_name().c_str(), -m_total_memory_storage, "%");

  // The function prologue will push %rbp, which should guarantee that the
  // stack pointer (%rsp) will contain an address that is a multiple of 16.
  // If the total memory storage required is not a multiple of 16, add to
  // it so that it is.

  if ((m_total_memory_storage) % 16 != 0)
    m_total_memory_storage += (16 - (m_total_memory_storage % 16));

  printf("/*FUNCTION %s: %d BYTES OF LOCAL STORAGE ALLOCATED IN STACK FRAME*/\n",m_function->get_name().c_str(),m_total_memory_storage);


  // Iterate through high level instructions
  for (auto i = hl_iseq->cbegin(); i != hl_iseq->cend(); ++i) {
    Instruction *hl_ins = *i;

    // If the high-level instruction has a label, define an equivalent
    // label in the low-level instruction sequence
    if (i.has_label())
      ll_iseq->define_label(i.get_label());

    // Translate the high-level instruction into one or more low-level instructions.
    // The first generated low-level instruction is annotated with a textual
    // representation of the high-level instruction.
    unsigned ll_idx = ll_iseq->get_length();
    translate_instruction(hl_ins, ll_iseq);
    HighLevelFormatter hl_formatter;
    ll_iseq->get_instruction(ll_idx)->set_comment(hl_formatter.format_instruction(hl_ins));
  }

  return ll_iseq;
}

// These helper functions are provided to make it easier to handle
// the way that instructions and operands vary based on operand size
// ('b'=1 byte, 'w'=2 bytes, 'l'=4 bytes, 'q'=8 bytes.)

// Check whether hl_opcode matches a range of opcodes, where base
// is a _b variant opcode. Return true if the hl opcode is any variant
// of that base.
bool match_hl(int base, int hl_opcode) {
  return hl_opcode >= base && hl_opcode < (base + 4);
}

// For a low-level instruction with 4 size variants, return the correct
// variant. base_opcode should be the "b" variant, and operand_size
// should be the operand size in bytes (1, 2, 4, or 8.)
LowLevelOpcode select_ll_opcode(LowLevelOpcode base_opcode, int operand_size) {
  int off;

  switch (operand_size) {
  case 1: // 'b' variant
    off = 0; break;
  case 2: // 'w' variant
    off = 1; break;
  case 4: // 'l' variant
    off = 2; break;
  case 8: // 'q' variant
    off = 3; break;
  default:
    assert(false);
    off = 3;
  }

  return LowLevelOpcode(int(base_opcode) + off);
}

// Get the correct Operand::Kind value for a machine register
// of the specified size (1, 2, 4, or 8 bytes.)
Operand::Kind select_mreg_kind(int operand_size) {
  switch (operand_size) {
  case 1:
    return Operand::MREG8;
  case 2:
    return Operand::MREG16;
  case 4:
    return Operand::MREG32;
  case 8:
    return Operand::MREG64;
  default:
    assert(false);
    return Operand::MREG64;
  }
}

void LowLevelCodeGen::translate_instruction(Instruction *hl_ins, std::shared_ptr<InstructionSequence> ll_iseq) {
  HighLevelOpcode hl_opcode = HighLevelOpcode(hl_ins->get_opcode());

  if (hl_opcode == HINS_enter) {
    // Function prologue: this will create an ABI-compliant stack frame.
    // The local variable area is *below* the address in %rbp, and local storage
    // can be accessed at negative offsets from %rbp. For example, the topmost
    // 4 bytes in the local storage area are at -4(%rbp).
    ll_iseq->append(new Instruction(MINS_PUSHQ, Operand(Operand::MREG64, MREG_RBP)));
    ll_iseq->append(new Instruction(MINS_MOVQ, Operand(Operand::MREG64, MREG_RSP), Operand(Operand::MREG64, MREG_RBP)));
    if (m_total_memory_storage > 0)
      ll_iseq->append(new Instruction(MINS_SUBQ, Operand(Operand::IMM_IVAL, m_total_memory_storage), Operand(Operand::MREG64, MREG_RSP)));
    return;
  }

  if (hl_opcode == HINS_leave) {
    // Function epilogue: deallocate local storage area and restore original value
    // of %rbp

    if (m_total_memory_storage > 0)
      ll_iseq->append(new Instruction(MINS_ADDQ, Operand(Operand::IMM_IVAL, m_total_memory_storage), Operand(Operand::MREG64, MREG_RSP)));
    ll_iseq->append(new Instruction(MINS_POPQ, Operand(Operand::MREG64, MREG_RBP)));

    return;
  }

  if (hl_opcode == HINS_ret) {
    ll_iseq->append(new Instruction(MINS_RET));
    return;
  }

  //IMPLEMENTING THE JMP INSTRUCTION
  if (hl_opcode == HINS_jmp) {
    //printf("JMP INSTRUCTION ENTERED\n");
    Operand dest_operand =
      get_ll_operand(hl_ins->get_operand(0), 0, ll_iseq);
    ll_iseq->append(new Instruction(MINS_JMP, dest_operand));
    return;
  }

  //IMPLEMENTING THE CONDITIONAL JUMP INSTRUCTIONS
  if ((hl_opcode == HINS_cjmp_t) || (hl_opcode == HINS_cjmp_f)) {
    //printf("CJMP INSTRUCTION ENTERED\n");
    LowLevelOpcode _opcode = MINS_CMPL;
    Operand cond_operand = get_ll_operand(hl_ins->get_operand(0), 4, ll_iseq);
    Operand imm_operand = Operand(Operand::IMM_IVAL, 0);

    ll_iseq->append(new Instruction(_opcode, imm_operand, cond_operand));

    int jump_opcode;
    hl_opcode == HINS_cjmp_t ? jump_opcode = MINS_JNE : jump_opcode = MINS_JE;

    ll_iseq->append(new Instruction(jump_opcode, hl_ins->get_operand(1)));
    return;
  }

  //IMPLEMENTING FUNCTION CALLS
  if ((hl_opcode == HINS_call)) {
    //printf("CALL INSTRUCTION ENTERED\n");
    ll_iseq->append(new Instruction(MINS_CALL, hl_ins->get_operand(0)));
    return;
  }

  //IMPLEMENTING THE LOCALADDR INSTRUCTION
  //Should consist of one leaq instruction loading the value at the correct index into %r10
  //Should then move %r10 into the destination register.
  if(hl_opcode == HINS_localaddr) {
    //printf("LOCALADDR INSTRUCTION ENTERED\n");
    LowLevelOpcode leaq_opcode = MINS_LEAQ;
    LowLevelOpcode mov_opcode = MINS_MOVQ;
    auto size = 8;

    //Create operands needed.
    Operand::Kind mreg_kind = select_mreg_kind(size);
    Operand r10(mreg_kind, MREG_R10);

    Operand dest_operand1 =
      get_ll_operand(hl_ins->get_operand(0), size, ll_iseq);

    //Calculate the offset, create operand
    auto off = hl_ins->get_operand(1).get_imm_ival();
    auto actual_off = -(m_local_storage + int(m_function->get_total_spilled_storage())) + (off);
    auto op_kind = Operand::MREG64_MEM_OFF;
    Operand mem_operand = Operand(op_kind, MREG_RBP, actual_off);

    ll_iseq->append(new Instruction(leaq_opcode, mem_operand, r10));
    ll_iseq->append(new Instruction(mov_opcode, r10, dest_operand1));

    return;
  }

  //IMPLEMENTING THE IMPLICIT CONVERSION INSTRUCTIONS
   if(hl_opcode == HINS_sconv_bl ||
      hl_opcode == HINS_sconv_bq ||
      hl_opcode == HINS_sconv_bw ||
      hl_opcode == HINS_sconv_lq ||
      hl_opcode == HINS_sconv_wl ||
      hl_opcode == HINS_sconv_wq ||
      hl_opcode == HINS_uconv_bl ||
      hl_opcode == HINS_uconv_bq ||
      hl_opcode == HINS_uconv_bw ||
      hl_opcode == HINS_uconv_lq ||
      hl_opcode == HINS_uconv_wl ||
      hl_opcode == HINS_uconv_wq){

     //printf("CONVERSION INSTRUCTION ENTERED\n");
     Operand mov1dest;
     Operand mov1sourc;
     Operand mov2dest;
     Operand mov2sourc;
     Operand mov3dest;
     Operand mov3sourc;

     LowLevelOpcode opcode1;
     LowLevelOpcode opcode2;
     LowLevelOpcode opcode3;

     switch(hl_opcode) {

       case(HINS_uconv_bl):
       case(HINS_sconv_bl):{
         int start_size = 1;
         int end_size = 4;

         mov1sourc = get_ll_operand(hl_ins->get_operand(1), start_size, ll_iseq);
         mov1dest = Operand(select_mreg_kind(start_size), MREG_R10);
         opcode1 = LowLevelOpcode::MINS_MOVB;

         mov2sourc = mov1dest;
         mov2dest = Operand(select_mreg_kind(end_size), MREG_R10);
         hl_opcode == HINS_sconv_bl ? opcode2 = MINS_MOVSBL : opcode2 = MINS_MOVZBL;

         mov3sourc = mov2dest;
         mov3dest = get_ll_operand(hl_ins->get_operand(0), end_size, ll_iseq);
         opcode3 = LowLevelOpcode::MINS_MOVL;
         break;
       }
       case(HINS_uconv_bq):
       case(HINS_sconv_bq):{
         int start_size = 1;
         int end_size = 8;

         mov1sourc = get_ll_operand(hl_ins->get_operand(1), start_size, ll_iseq);
         mov1dest = Operand(select_mreg_kind(start_size), MREG_R10);
         opcode1 = LowLevelOpcode::MINS_MOVB;

         mov2sourc = mov1dest;
         mov2dest = Operand(select_mreg_kind(end_size), MREG_R10);
         hl_opcode == HINS_sconv_bq ? opcode2 = MINS_MOVSBQ : opcode2 = MINS_MOVZBQ;

         mov3sourc = mov2dest;
         mov3dest = get_ll_operand(hl_ins->get_operand(0), end_size, ll_iseq);
         opcode3 = LowLevelOpcode::MINS_MOVQ;
         break;
       }
       case(HINS_uconv_bw):
       case(HINS_sconv_bw):{
         int start_size = 1;
         int end_size = 2;

         mov1sourc = get_ll_operand(hl_ins->get_operand(1), start_size, ll_iseq);
         mov1dest = Operand(select_mreg_kind(start_size), MREG_R10);
         opcode1 = LowLevelOpcode::MINS_MOVB;

         mov2sourc = mov1dest;
         mov2dest = Operand(select_mreg_kind(end_size), MREG_R10);
         hl_opcode == HINS_sconv_bw ? opcode2 = MINS_MOVSBW : opcode2 = MINS_MOVZBW;

         mov3sourc = mov2dest;
         mov3dest = get_ll_operand(hl_ins->get_operand(0), end_size, ll_iseq);
         opcode3 = LowLevelOpcode::MINS_MOVW;
         break;
       }
       case(HINS_uconv_lq):
       case(HINS_sconv_lq): {
         //printf("HINS_SCONV_LQ\n");
         int start_size = 4;
         int end_size = 8;

         mov1sourc = get_ll_operand(hl_ins->get_operand(1), start_size, ll_iseq);
         mov1dest = Operand(select_mreg_kind(start_size), MREG_R10);
         opcode1 = LowLevelOpcode::MINS_MOVL;

         mov2sourc = mov1dest;
         mov2dest = Operand(select_mreg_kind(end_size), MREG_R10);
         if(hl_opcode == HINS_sconv_lq) {
           opcode2 = MINS_MOVSLQ;
         }
         else {
           opcode2 = MINS_MOVZLQ;
         }
         mov3sourc = mov2dest;
         mov3dest = get_ll_operand(hl_ins->get_operand(0), end_size, ll_iseq);
         opcode3 = LowLevelOpcode::MINS_MOVQ;
         break;
       }
       case(HINS_uconv_wl):
       case(HINS_sconv_wl): {
         int start_size = 2;
         int end_size = 4;

         mov1sourc = get_ll_operand(hl_ins->get_operand(1), start_size, ll_iseq);
         mov1dest = Operand(select_mreg_kind(start_size), MREG_R10);
         opcode1 = LowLevelOpcode::MINS_MOVW;

         mov2sourc = mov1dest;
         mov2dest = Operand(select_mreg_kind(end_size), MREG_R10);
         hl_opcode == HINS_sconv_wl ? opcode2 = MINS_MOVSWL : opcode2 = MINS_MOVZWL;

         mov3sourc = mov2dest;
         mov3dest = get_ll_operand(hl_ins->get_operand(0), end_size, ll_iseq);
         opcode3 = LowLevelOpcode::MINS_MOVL;
         break;
       }
       case(HINS_uconv_wq):
       case(HINS_sconv_wq): {
         int start_size = 2;
         int end_size = 8;

         mov1sourc = get_ll_operand(hl_ins->get_operand(1), start_size, ll_iseq);
         mov1dest = Operand(select_mreg_kind(start_size), MREG_R10);
         opcode1 = LowLevelOpcode::MINS_MOVW;

         mov2sourc = mov1dest;
         mov2dest = Operand(select_mreg_kind(end_size), MREG_R10);
         hl_opcode == HINS_sconv_wq ? opcode2 = MINS_MOVSWQ : opcode2 = MINS_MOVZWQ;

         mov3sourc = mov2dest;
         mov3dest = get_ll_operand(hl_ins->get_operand(0), end_size, ll_iseq);
         opcode3 = LowLevelOpcode::MINS_MOVQ;
         break;
       }
       default: {
         RuntimeError::raise("high level opcode Implicit Conversion %d not handled", int(hl_opcode));
       }
     }

     ll_iseq->append(new Instruction(opcode1, mov1sourc, mov1dest));
     ll_iseq->append(new Instruction(opcode2, mov2sourc, mov2dest));
     ll_iseq->append(new Instruction(opcode3, mov3sourc, mov3dest));

    return;
  }

  //IMPLEMENTING THE MOV_ INSTRUCTION
  //MATCH_HL LETS US CREATE ONE IF STATEMENT FOR ALL SUFFIXES OF MOV
  if (match_hl(HINS_mov_b, hl_opcode)) {
    //printf("MOV INSTRUCTION ENTERED\n");
    int size = highlevel_opcode_get_source_operand_size(hl_opcode);

    LowLevelOpcode mov_opcode = select_ll_opcode(MINS_MOVB, size);

    Operand src_operand = get_ll_operand(hl_ins->get_operand(1), size, ll_iseq);
    Operand dest_operand = get_ll_operand(hl_ins->get_operand(0), size, ll_iseq);

    if (src_operand.is_memref() && dest_operand.is_memref()) {
      // move source operand into a temporary register
      Operand::Kind mreg_kind = select_mreg_kind(size);
      Operand r10(mreg_kind, MREG_R10);
      ll_iseq->append(new Instruction(mov_opcode, src_operand, r10));
      src_operand = r10;
    }
    ll_iseq->append(
      new Instruction(mov_opcode, src_operand, dest_operand)
    );
    return;
  }

  //IMPLEMENTING THE ADD_, SUB_ INSTRUCTIONS
  if (match_hl(HINS_add_b, hl_opcode) ||
      match_hl(HINS_sub_b, hl_opcode)){

    //printf("ADD/SUB INSTRUCTION ENTERED\n");

    int size = highlevel_opcode_get_source_operand_size(hl_opcode);
    LowLevelOpcode mov_opcode = select_ll_opcode(MINS_MOVB, size);
    LowLevelOpcode _opcode;
    if(match_hl(HINS_add_b, hl_opcode)) _opcode = select_ll_opcode(MINS_ADDB, size);
    if(match_hl(HINS_sub_b, hl_opcode)) _opcode = select_ll_opcode(MINS_SUBB, size);
    Operand src_operand1 =
      get_ll_operand(hl_ins->get_operand(1), size, ll_iseq);
    Operand src_operand2 =
      get_ll_operand(hl_ins->get_operand(2), size, ll_iseq);
    Operand dest_operand =
      get_ll_operand(hl_ins->get_operand(0), size, ll_iseq);

    // move source operand into a temporary register
    Operand::Kind mreg_kind = select_mreg_kind(size);
    Operand r10(mreg_kind, MREG_R10);
    ll_iseq->append(new Instruction(mov_opcode, src_operand1, r10));
    src_operand1 = r10;
    ll_iseq->append(new Instruction(_opcode, src_operand2, src_operand1));
    ll_iseq->append(new Instruction(mov_opcode, src_operand1, dest_operand));
    return;
  }

  //IMPLEMENTING THE MUL AND DIV INSTRUCTIONS
  if(match_hl(HINS_mul_b, hl_opcode)){
    //printf("MUL/DIV INSTRUCTION ENTERED\n");
    Operand mov1dest;
    Operand mov1sourc;
    Operand mov2dest;
    Operand mov2sourc;
    Operand mov3dest;
    Operand mov3sourc;

    LowLevelOpcode opcode1;
    LowLevelOpcode opcode2;
    LowLevelOpcode opcode3;

    int size = highlevel_opcode_get_source_operand_size(hl_opcode);

    mov1sourc = get_ll_operand(hl_ins->get_operand(1), size, ll_iseq);
    mov1dest = Operand(select_mreg_kind(size), MREG_R10);
    opcode1 = select_ll_opcode(MINS_MOVB, size);

    mov2sourc = get_ll_operand(hl_ins->get_operand(2), size, ll_iseq);
    mov2dest = mov1dest;
    opcode2 =  size == 4 ? MINS_IMULL : MINS_IMULQ;

    mov3sourc = mov2dest;
    mov3dest = get_ll_operand(hl_ins->get_operand(0), size, ll_iseq);
    opcode3 = select_ll_opcode(MINS_MOVB, size);

    ll_iseq->append(new Instruction(opcode1, mov1sourc, mov1dest));
    ll_iseq->append(new Instruction(opcode2, mov2sourc, mov2dest));
    ll_iseq->append(new Instruction(opcode3, mov3sourc, mov3dest));

    return;
  }

  //IMPLEMENTING THE DIV INSTRUCTION
  if(match_hl(HINS_div_b, hl_opcode) ||
     match_hl(HINS_mod_b, hl_opcode)) {
    //Algorithm:
    //Move operand 1 into %ax
    //Emit CDQ instruction
    //Move operand 2 into %r10
    //Emit DIV instruction using %r10 as only operand
    //Mov %ax into operand 0.

    Operand _1dest;
    Operand _1sourc;
    Operand _2dest;
    Operand _2sourc;
    Operand _3op;
    Operand _4dest;
    Operand _4sourc;


    LowLevelOpcode opcode1;
    LowLevelOpcode opcode2;
    LowLevelOpcode opcode3;
    LowLevelOpcode opcode4;

    int size = highlevel_opcode_get_source_operand_size(hl_opcode);

    _1sourc = get_ll_operand(hl_ins->get_operand(1), size, ll_iseq);
    _1dest = Operand(select_mreg_kind(size), MREG_RAX);
    opcode1 = select_ll_opcode(MINS_MOVB, size);

    _2sourc = get_ll_operand(hl_ins->get_operand(2), size, ll_iseq);
    _2dest = Operand(select_mreg_kind(size), MREG_R10);
    opcode2 = select_ll_opcode(MINS_MOVB, size);

    _3op = _2dest;
    opcode3 = size == 4 ? MINS_IDIVL : MINS_IDIVQ;

    if(match_hl(HINS_div_b, hl_opcode)) {
      _4sourc = _1dest;
    }
    else {
      _4sourc = Operand(select_mreg_kind(size), MREG_RDX);
    }
    _4dest = get_ll_operand(hl_ins->get_operand(0), size, ll_iseq);
    opcode4 = select_ll_opcode(MINS_MOVB, size);

    ll_iseq->append(new Instruction(opcode1, _1sourc, _1dest));
    ll_iseq->append(new Instruction(MINS_CDQ));
    ll_iseq->append(new Instruction(opcode2, _2sourc, _2dest));
    ll_iseq->append(new Instruction(opcode3, _3op));
    ll_iseq->append(new Instruction(opcode4, _4sourc, _4dest));

    return;
  }

  //IMPLEMENTING THE CMP_B INSTRUCTIONS
  if (match_hl(HINS_cmplt_b, hl_opcode) ||
      match_hl(HINS_cmpeq_b, hl_opcode) ||
      match_hl(HINS_cmpgt_b, hl_opcode) ||
      match_hl(HINS_cmpgte_b, hl_opcode)||
      match_hl(HINS_cmplte_b, hl_opcode) ||
      match_hl(HINS_cmpneq_b, hl_opcode)){

    //printf("CMP_B INSTRUCTION ENTERED\n");

    int size = highlevel_opcode_get_source_operand_size(hl_opcode);

    LowLevelOpcode mov_opcode = select_ll_opcode(MINS_MOVB, size);
    LowLevelOpcode cmp_opcode = select_ll_opcode(MINS_CMPB, size);
    LowLevelOpcode mov_opcode2 = MINS_MOVZBL;

    Operand::Kind mreg_kind = select_mreg_kind(size);
    Operand r10(mreg_kind, MREG_R10);
    Operand r11(mreg_kind, MREG_R11);

    Operand src_operand1 =
      get_ll_operand(hl_ins->get_operand(1), size, ll_iseq);
    Operand src_operand2 =
      get_ll_operand(hl_ins->get_operand(2), size, ll_iseq);
    Operand dest_operand =
      get_ll_operand(hl_ins->get_operand(0), size, ll_iseq);

    ll_iseq->append(new Instruction(mov_opcode, src_operand1, r10));
    src_operand1 = r10;

    ll_iseq->append(new Instruction(cmp_opcode, src_operand2, src_operand1));

    src_operand1 = Operand(Operand::MREG8, src_operand1.get_base_reg());

    if(match_hl(HINS_cmplt_b, hl_opcode)) {
      ll_iseq->append(
      new Instruction(MINS_SETL, src_operand1)
      );
    }
    else if(match_hl(HINS_cmpeq_b, hl_opcode)) {
      ll_iseq->append(
      new Instruction(MINS_SETE, src_operand1)
      );
    }
    else if(match_hl(HINS_cmpgt_b, hl_opcode)) {
      ll_iseq->append(
      new Instruction(MINS_SETG, src_operand1)
      );
    }
    else if(match_hl(HINS_cmpgte_b, hl_opcode)) {
      ll_iseq->append(
      new Instruction(MINS_SETGE, src_operand1)
      );
    }
    else if(match_hl(HINS_cmplte_b, hl_opcode)) {
      ll_iseq->append(
      new Instruction(MINS_SETLE, src_operand1)
      );
    }
    else if(match_hl(HINS_cmpneq_b, hl_opcode)) {
      ll_iseq->append(
      new Instruction(MINS_SETNE, src_operand1)
      );
    }

    ll_iseq->append(
      new Instruction(mov_opcode2, src_operand1, r11)
      );
    src_operand1 = r11;

    ll_iseq->append(
      new Instruction(mov_opcode, src_operand1, dest_operand)
      );

    return;
  }

  //IMPLEMENTING THE NEGATE INSTRUCTION
  if(match_hl(HINS_neg_b, hl_opcode)) {
    //Need to:
    //1. Move Op1 into %r10
    //2. Move 0 into Op2
    //3. Subtract %r10, Op2

    Operand mov1dest;
    Operand mov1sourc;
    Operand mov2dest;
    Operand mov2sourc;
    Operand mov3dest;
    Operand mov3sourc;

    LowLevelOpcode opcode1;
    LowLevelOpcode opcode2;
    LowLevelOpcode opcode3;

    int size = highlevel_opcode_get_source_operand_size(hl_opcode);

    mov1sourc = get_ll_operand(hl_ins->get_operand(1), size, ll_iseq);
    mov1dest = Operand(select_mreg_kind(size), MREG_R10);
    opcode1 = select_ll_opcode(MINS_MOVB, size);

    mov2sourc = Operand(Operand::IMM_IVAL, 0);
    mov2dest = get_ll_operand(hl_ins->get_operand(0), size, ll_iseq);
    opcode2 = select_ll_opcode(MINS_MOVB, size);

    mov3sourc = mov1dest;
    mov3dest = mov2dest;
    opcode3 = select_ll_opcode(MINS_SUBB, size);

    ll_iseq->append(new Instruction(opcode1, mov1sourc, mov1dest));
    ll_iseq->append(new Instruction(opcode2, mov2sourc, mov2dest));
    ll_iseq->append(new Instruction(opcode3, mov3sourc, mov3dest));

    return;

  }

  //IMPLEMENTING OTHER INSTRUCTIONS (INSTRUCTIONS WHICH ARE NOT USED IN THE TESTS)

  //IMPLEMENTING NOP INSTRUCTION
  if(hl_opcode == HINS_nop) {
    ll_iseq->append(new Instruction(MINS_NOP));
    return;
  }


  //IMPLEMENTING THE NOT INSTRUCTION - NOT HANDLED


  //IMPLEMENTING THE AND INSTRUCTION - NOT HANDLED


  //IMPLEMENTING THE OR INSTRUCTION - NOT HANDLED


  //IMPLEMENTING THE XOR INSTRUCTION - NOT HANDLED

  if(match_hl(HINS_spill_b, hl_opcode)) {
    int size = highlevel_opcode_get_source_operand_size(hl_opcode);
    auto hl_op1 = hl_ins->get_operand(0);
    auto hl_op2 = hl_ins->get_operand(1);
    LowLevelOpcode mov_opcode = select_ll_opcode(MINS_MOVB, size);
    Operand operand1 = get_ll_operand(hl_op1, size, ll_iseq);
    auto offset = hl_op2.get_imm_ival();
    auto operand2 = Operand(Operand::MREG64_MEM_OFF, MREG_RBP, offset);
    ll_iseq->append(new Instruction(mov_opcode, operand1, operand2));
    return;
  }

  if(match_hl(HINS_restore_b, hl_opcode)) {
    int size = highlevel_opcode_get_source_operand_size(hl_opcode);
    auto hl_op1 = hl_ins->get_operand(0);
    auto hl_op2 = hl_ins->get_operand(1);
    LowLevelOpcode mov_opcode = select_ll_opcode(MINS_MOVB, size);
    Operand operand2 = get_ll_operand(hl_op1, size, ll_iseq);
    auto offset = hl_op2.get_imm_ival();
    auto operand1 = Operand(Operand::MREG64_MEM_OFF, MREG_RBP, offset);
    ll_iseq->append(new Instruction(mov_opcode, operand1, operand2));
    return;
  }

  RuntimeError::raise("high level opcode %d not handled", int(hl_opcode));
}

// Get_ll_operand needs to be defined - currently only declared?

//ARGUMENTS:  Takes an hl_opcode, a size (source operand size) and an instructionsequence.
//PURPOSE:    Computes the corresponding ll_operand and returns this.
//            Algorithm:
//            1. Look at HL kind.
//            2. If VREG then:
//                a) If base_register >= 10 set ll_opcode to MREG_64_MEM_OFF with appropriate offset
//                b) If base_register <= 10 set ll_opcode to the correct kind and correct number.
//            3. If VREG_MEM then:
//                a) Create mov instruction using R11.
//            4. If IMM, IMM_LABEL or LABEL
//                a) simple case, simple return the IMM, IMM_LABEL or LABEL.
Operand LowLevelCodeGen::get_ll_operand(Operand hl_operand, int size, std::shared_ptr<InstructionSequence> ll_iseq) {
  auto hl_kind = hl_operand.get_kind();
  auto MREG = static_cast<MachineReg>(hl_operand.get_MachineReg());
  Operand op;

  if(MREG >= MREG_END) {
    if(hl_kind == Operand::VREG || hl_kind == Operand::VREG_MEM) {
      auto hl_reg = hl_operand.get_base_reg();
      if(hl_reg >= 10) {
        //These are parameter register, local registers and temporary registers.
        //All of these should be saved in memory. We need to find the correct offset.
        //Assume: Registers are allocated room AFTER the memory based entiteties (arrays,structs...)
        //Assume: Registers are allocated in the following order: VR10 is furthest from RBP.
        auto offset = -(m_local_storage + (m_register_storage - (8 * (hl_reg-10))));
        auto op_kind = Operand::MREG64_MEM_OFF;
        op = Operand(op_kind, MREG_RBP, offset);
      }
      else if (hl_reg == 0) {
        auto op_kind = select_mreg_kind(size);
        op = Operand(op_kind, MREG_RAX);    // USED FOR RETURNS
      }
      else if (hl_reg == 1) {
        auto op_kind = select_mreg_kind(size);
        op = Operand(op_kind, MREG_RDI);    // FIRST ARGUMENT REG
      }
      else if (hl_reg == 2) {
        auto op_kind = select_mreg_kind(size);
        op = Operand(op_kind, MREG_RSI);    // SECOND ARGUMENT REG
      }
      else if (hl_reg == 3) {
        auto op_kind = select_mreg_kind(size);  // THIRD ARGUMENT REG
        op = Operand(op_kind, MREG_RDX);
      }
      else if (hl_reg == 4) {
        auto op_kind = select_mreg_kind(size);  // FOURTH ARGUMENT REG
        op = Operand(op_kind, MREG_RCX);
      }
      else if (hl_reg == 5) {
        auto op_kind = select_mreg_kind(size);  // FIFTH ARGUMENT REG
        op = Operand(op_kind, MREG_R8);
      }
      else if (hl_reg == 6) {
        auto op_kind = select_mreg_kind(size);  // SIXTH ARGUMENT REG
        op = Operand(op_kind, MREG_R9);
      }
      else {
        assert(false);
      }
      if (hl_kind == Operand::VREG_MEM) {
        LowLevelOpcode opcode = MINS_MOVQ;
        Operand::Kind mreg_kind = Operand::MREG64;
        Operand r11(mreg_kind, MREG_R11);
        ll_iseq->append(new Instruction(opcode, op, r11));
        op = r11.to_memref();
      }
      return op;
    }
    if (hl_kind == Operand::IMM_IVAL){return Operand(Operand::IMM_IVAL,  hl_operand.get_imm_ival());}
    if (hl_kind == Operand::IMM_LABEL){return Operand(Operand::IMM_LABEL,  hl_operand.get_label());}
    if (hl_kind == Operand::LABEL){return Operand(Operand::LABEL,  hl_operand.get_label());}
  }
  else {
    if(hl_operand.is_memref()){op = Operand(Operand::MREG64_MEM, MREG);}
    else {
      switch(size) {
        case 1: {op = Operand(Operand::MREG8 , MREG); break;}
        case 2: {op = Operand(Operand::MREG16, MREG); break;}
        case 4: {op = Operand(Operand::MREG32, MREG); break;}
        case 8: {op = Operand(Operand::MREG64, MREG); break;}
        default:{op = Operand(Operand::MREG64, MREG); break;}
      }
    }
  }
  return op;
}

