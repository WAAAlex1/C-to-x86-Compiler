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
#include "node.h"
#include "instruction.h"
#include "highlevel.h"
#include "ast.h"
#include "parse.tab.h"
#include "grammar_symbols.h"
#include "exceptions.h"
#include "local_storage_allocation.h"
#include "highlevel_codegen.h"

#include <csetjmp>


// Adjust an opcode for a basic type
HighLevelOpcode get_opcode(HighLevelOpcode base_opcode, std::shared_ptr<Type> type) {
  if (type->is_basic())
    return static_cast<HighLevelOpcode>(int(base_opcode) + int(type->get_basic_type_kind()));
  else if (type->is_pointer())
    return static_cast<HighLevelOpcode>(int(base_opcode) + int(BasicTypeKind::LONG));
  else
    RuntimeError::raise("attempt to use type '%s' as data in opcode selection", type->as_str().c_str());
}

HighLevelCodegen::HighLevelCodegen(const Options &options, int next_label_num)
  : m_options(options)
  , m_next_label_num(next_label_num)
{
}

HighLevelCodegen::~HighLevelCodegen() {
}

void HighLevelCodegen::generate(std::shared_ptr<Function> function) {
  assert(function->get_funcdef_ast() != nullptr);
  assert(!function->get_hl_iseq());

  // Create empty InstructionSequence to hold high-level instructions
  std::shared_ptr<InstructionSequence> hl_iseq(new InstructionSequence());
  function->set_hl_iseq(hl_iseq);

  // Member functions can use m_function to access the Function object
  m_function = function;
  auto num_local_regs = function->get_vregAlloc()->enter_block() - 10; //EDITED LRA
  m_function->set_num_loc_regs(num_local_regs);                           //EDITED LRA
  // Visit function definition
  visit(function->get_funcdef_ast());
}

void HighLevelCodegen::visit_function_definition(Node *n) {
  // generate the name of the label that return instructions should target
  std::string fn_name = n->get_kid(1)->get_str();
  m_return_label_name = ".L" + fn_name + "_return";

  unsigned total_local_storage = 0U;
  total_local_storage = m_function->get_total_storage();

  get_hl_iseq()->append(new Instruction(HINS_enter, Operand(Operand::IMM_IVAL, total_local_storage)));

  //Emit mov instructions to move all relevant argument registers
  //into the allocated parameter registers
  auto param_list = n->get_kid(2); //get the param_list;
  auto arg_reg_num = 1;
  for(auto i = 0U; i < param_list->get_num_kids(); i++) {
    auto param_sym = param_list->get_kid(i)->get_symbol_ptr();
    auto op_base = param_sym->get_Operand().get_base_reg();
    auto dest = Operand(Operand::VREG, op_base);
    auto arg_reg_op = Operand(Operand::VREG, arg_reg_num);
    auto opcode = get_opcode(HINS_mov_b, param_sym->get_type());
    get_hl_iseq()->append(new Instruction(opcode, dest,arg_reg_op));
    arg_reg_num++;
  }

  // visit body
  visit(n->get_kid(3));

  get_hl_iseq()->define_label(m_return_label_name);
  get_hl_iseq()->append(new Instruction(HINS_leave, Operand(Operand::IMM_IVAL, total_local_storage)));
  get_hl_iseq()->append(new Instruction(HINS_ret));
}

void HighLevelCodegen::visit_statement_list(Node *n) {
  //For the statement list we should:
  //  A: Visit all children.
  //  B: Assuming that temperorary variables are only valid for one statement
  //     Reset the variable count back to m_top after each statement.

  // This should hence not generate any code itself.
  auto num_stmt = n->get_num_kids();

  for(auto i = 0U; i < num_stmt; i++) {
    visit(n->get_kid(i)); //Visit statement
  }
}

void HighLevelCodegen::visit_expression_statement(Node *n) {
  //Expression statement needs to:

  // 1. Visit child
  //      - Child could be:
  //          - BINARY EXPRESSION
  //          - UNARY EXPRESSION

  //This function seems useless
  visit(n->get_kid(0));

}

void HighLevelCodegen::visit_return_statement(Node *n) {
  //Emit a jump instruction to function return label

  HighLevelOpcode jmp_opcode = HINS_jmp;
  auto return_label = m_return_label_name;

  //Append one operand jmp instruction in which operand is label type with return_label
  get_hl_iseq()->append(new Instruction(jmp_opcode, Operand(Operand::LABEL, return_label)));
}

void HighLevelCodegen::visit_return_expression_statement(Node *n) {
  // A possible implementation:

  Node *expr = n->get_kid(0);

  // generate code to evaluate the expression
  visit(expr);

  // move the computed value to the return value vreg
  HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, expr->get_type());
  get_hl_iseq()->append(new Instruction(mov_opcode, Operand(Operand::VREG, LocalStorageAllocation::VREG_RETVAL), expr->get_operand()));

  // jump to the return label
  visit_return_statement(n);

}

void HighLevelCodegen::visit_while_statement(Node *n) {
  // GENERAL STRUCTURE:
  // jmp .L1;
  // L0:
  // - Body of while statement (visit child (1))
  // L1:
  // - control statement (visit child(0))
  // - cjmp_t .L0

  //PROCEDURE:
  // 1. Create labels
  auto body_label = next_label();
  auto control_label = next_label();
  // 2. Emit jmp .L1 instruction
  auto L1 = Operand(Operand::LABEL, control_label);
  get_hl_iseq()->append(new Instruction(HINS_jmp, L1));
  // 3. Emit L0 label
  get_hl_iseq()->define_label(body_label);
  // 4. Visit child(1)
  visit(n->get_kid(1));
  // 5. Emit JMP .L1 instruction
  get_hl_iseq()->append(new Instruction(HINS_jmp, L1));
  // 5. Emit L1 label
  get_hl_iseq()->define_label(control_label);
  // 6. Visit child(0)
  visit(n->get_kid(0));
  // 7. Emit cjmp_t .L0 instruction
  auto control_reg = n->get_kid(0)->get_operand().get_base_reg();
  auto control_op = Operand(Operand::VREG, control_reg);
  auto L0 = Operand(Operand::LABEL, body_label);
  get_hl_iseq()->append(new Instruction(HINS_cjmp_t, control_op, L0));

  //Can't imagine why we would want to annotate this node with an operand

}

void HighLevelCodegen::visit_do_while_statement(Node *n) {
  // Should be the same as the do_while_statement besides from:
  // The body should be traversed once before the control statement is checked
  // Also order of children is different than while_statement

  //Only need one label (for the body)
  //Dont need to emit jmp instruction at start.

  //PROCEDURE:
  // 1. Create label
  auto body_label = next_label();
  // 2. Create JMP .L0 instruction
  auto L0 = Operand(Operand::LABEL, body_label);
  get_hl_iseq()->append(new Instruction(HINS_jmp, L0));
  // 3. Emit L0 label
  get_hl_iseq()->define_label(body_label);
  // 4. Visit child(0)
  visit(n->get_kid(0));
  // 6. Visit child(1)
  visit(n->get_kid(1));
  // 7. Emit cjmp_t .L0 instruction
  auto control_reg = n->get_kid(1)->get_operand().get_base_reg();
  auto control_op = Operand(Operand::VREG, control_reg);
  get_hl_iseq()->append(new Instruction(HINS_cjmp_t, control_op, L0));

  //Cant think of reason for annotating node with operand in this case
}

void HighLevelCodegen::visit_for_statement(Node *n) {
  // PROCEDURE:
  // Create labels
  auto body_label = next_label();
  auto control_label = next_label();
  // Visit Child(0) - initial assignment of control variable
  visit(n->get_kid(0));
  // Emit JMP L1 instruction
  auto L1 = Operand(Operand::LABEL, control_label);
  get_hl_iseq()->append(new Instruction(HINS_jmp, L1));
  // Create Label .L0
  get_hl_iseq()->define_label(body_label);
  // Visit Child(3) - Statement list
  visit(n->get_kid(3));
  // Visit Child(2) - Increment of control variable
  visit(n->get_kid(2));
  // Emit jmp .L1 instruction
  get_hl_iseq()->append(new Instruction(HINS_jmp, L1));
  // Create Label .L1
  get_hl_iseq()->define_label(control_label);
  // Visit Child(1) - Control logic
  visit(n->get_kid(1));
  // Emit CJMP_t L0 Instruction
  auto L0 = Operand(Operand::LABEL, body_label);
  auto control_reg = n->get_kid(1)->get_operand().get_base_reg();
  auto control_op = Operand(Operand::VREG, control_reg);
  get_hl_iseq()->append(new Instruction(HINS_cjmp_t, control_op, L0));

  //cant find reason for annotating node with operand
}

void HighLevelCodegen::visit_if_statement(Node *n)   {
  // Create label
  auto end_label = next_label();
  // visit child(0) - control statement
  visit(n->get_kid(0));
  // Emit cjmp_f .L0 instruction
  auto L0 = Operand(Operand::LABEL, end_label);
  auto control_reg = n->get_kid(0)->get_operand().get_base_reg();
  auto control_op = Operand(Operand::VREG, control_reg);
  get_hl_iseq()->append(new Instruction(HINS_cjmp_f, control_op, L0));
  // Visit child(1) - statement list
  visit(n->get_kid(1));
  // Emit jmp .L0 instruction
  get_hl_iseq()->append(new Instruction(HINS_jmp,  L0));
  // Define Label .L0
  get_hl_iseq()->define_label(end_label);
}

void HighLevelCodegen::visit_if_else_statement(Node *n) {
  //Basically the same as visit_if_statement
  //Need one additional label for the else case
  //Need one additional jump instruction to skip the else case
  // Create label
  auto end_label = next_label();
  auto false_label = next_label();
  // visit child(0) - control statement
  visit(n->get_kid(0));
  // Emit cjmp_f .L1 instruction
  auto L1 = Operand(Operand::LABEL, false_label);
  auto control_reg = n->get_kid(0)->get_operand().get_base_reg();
  auto control_op = Operand(Operand::VREG, control_reg);
  get_hl_iseq()->append(new Instruction(HINS_cjmp_f, control_op, L1));
  // Visit child(1) - statement list (true)
  visit(n->get_kid(1));
  // Emit jmp .L0 instruction
  auto L0 = Operand(Operand::LABEL, end_label);
  get_hl_iseq()->append(new Instruction(HINS_jmp,  L0));
  // Define Label .L1
  get_hl_iseq()->define_label(false_label);
  // Visit child(2) - statement list (false)
  visit(n->get_kid(2));
  // Emit jmp .L0 instruction
  get_hl_iseq()->append(new Instruction(HINS_jmp,  L0));
  // Define end label
  get_hl_iseq()->define_label(end_label);

}

void HighLevelCodegen::visit_binary_expression(Node *n) {
  auto op = n->get_kid(0);
  auto op_tag = op->get_tag();
  auto lop = n->get_kid(1);
  auto rop = n->get_kid(2);

  //Generate code to evaluate the expression
  visit(rop);
  visit(lop);

  //Allocate temporary register to hold result
  auto vregAlloc = m_function->get_vregAlloc();
  int temp_reg;

  //Special case for not allocating a temporary register
  if(op_tag == TOK_ASSIGN) {
    temp_reg = lop->get_operand().get_base_reg();
  }
  else {
    temp_reg = vregAlloc->alloc_temp();
  }

  HighLevelOpcode opcode;
  //Instruction opcode based on the type of op
  //For choosing correct suffix of opcode type stored in expr used
  switch (op_tag) {
    case TOK_MINUS: {
      opcode = get_opcode(HINS_sub_b, n->get_type());
      break;
    }
    case TOK_PLUS: {
      opcode = get_opcode(HINS_add_b, n->get_type());
      break;
    }
    case TOK_MOD: {
      opcode = get_opcode(HINS_mod_b, n->get_type());
      break;
    }
    case TOK_DIVIDE: {
      opcode = get_opcode(HINS_div_b, n->get_type());
      break;
    }
    case TOK_ASTERISK: {
      opcode = get_opcode(HINS_mul_b, n->get_type());
      break;
    }
    case TOK_ASSIGN: {
      opcode = get_opcode(HINS_mov_b, n->get_type());
      break;
    }
    case TOK_LOGICAL_OR: {
      opcode = get_opcode(HINS_or_b, n->get_type());
      break;
    }
    case TOK_LOGICAL_AND: {
      opcode = get_opcode(HINS_and_b, n->get_type());
      break;
    }
    case TOK_INEQUALITY: {
      opcode = get_opcode(HINS_cmpneq_b, n->get_type());
      break;
    }
    case TOK_EQUALITY: {
      opcode = get_opcode(HINS_cmpeq_b, n->get_type());
      break;
    }
    case TOK_GTE: {
      opcode = get_opcode(HINS_cmpgte_b, n->get_type());
      break;
    }
    case TOK_GT: {
      opcode = get_opcode(HINS_cmpgt_b, n->get_type());
      break;
    }
    case TOK_LTE: {
      opcode = get_opcode(HINS_cmplte_b, n->get_type());
      break;
    }
    case TOK_LT: {
      opcode = get_opcode(HINS_cmplt_b, n->get_type());
      break;
    }
    default: {
      opcode = HINS_nop;
      break;
    }
  }

  //Special case for not allocating a temporary register
  if(op_tag == TOK_ASSIGN) {
    //MOV instruction is only 2 operands
    auto LOP = lop->get_operand();
    //printf("BASE REG LEFT: %d\n", LOP.get_base_reg());
    auto ROP = rop->get_operand();
    //printf("BASE REG RIGHT: %d\n", ROP.get_base_reg());
    auto dest = Operand(Operand::VREG, temp_reg);
    get_hl_iseq()->append(new Instruction(opcode, LOP, ROP));
    //printf("OPCODE: %d\n", opcode);
    //Make sure to annotate node with operand
    n->set_operand(dest);
  }
  else {
    //All other binary_expr instructions are 3 operands
    auto LOP = lop->get_operand();
    auto ROP = rop->get_operand();
    //If both are memory operands this will give us issues in low-level codegen.
    //Hence we move ROP to a temp vreg and emit a mov instruction.
    if(LOP.is_memref() && ROP.is_memref()) {
      auto reg = vregAlloc->alloc_temp();
      auto op2 = Operand(Operand::VREG, reg);
      get_hl_iseq()->append(new Instruction(HINS_mov_q, op2, ROP));
      ROP = op2;
    }
    auto dest = Operand(Operand::VREG, temp_reg);
    get_hl_iseq()->append(new Instruction(opcode, dest, LOP, ROP));

    //Make sure to annotate node with operand
    n->set_operand(dest);
  }
}

void HighLevelCodegen::visit_unary_expression(Node *n) {
  auto op = n->get_kid(0);
  auto op_tag = op->get_tag();
  auto operand = n->get_kid(1);

  //Generate code to evaluate the expression
  visit(operand);

  //Allocate temporary register to hold result
  auto vregAlloc = m_function->get_vregAlloc();
  int temp_reg = 0;

  HighLevelOpcode opcode;
  //Instruction opcode based on the type of op
  //For choosing correct suffix of opcode type stored in expr used
  switch (op_tag) {
    case TOK_MINUS: {
      //Code emitted
      opcode = get_opcode(HINS_neg_b, n->get_type());
      temp_reg = vregAlloc->alloc_temp();

      //Use operand in codegen
      auto OP = operand->get_operand();
      auto dest = Operand(Operand::VREG, temp_reg);
      get_hl_iseq()->append(new Instruction(opcode, dest, OP));

      //Make sure to annotate node with operand
      n->set_operand(dest);

      break;
    }
    case TOK_BITWISE_COMPL:{
      //Code emitted
      opcode = get_opcode(HINS_compl_b, n->get_type());
      temp_reg = vregAlloc->alloc_temp();

      //Use operand in codegen
      auto OP = operand->get_operand();
      auto dest = Operand(Operand::VREG, temp_reg);
      get_hl_iseq()->append(new Instruction(opcode, dest, OP));

      //Make sure to annotate node with operand
      n->set_operand(dest);

      break;
    }
    case TOK_NOT: {
      //Code emitted
      opcode = get_opcode(HINS_not_b, n->get_type());
      temp_reg = vregAlloc->alloc_temp();

      //Use operand in codegen
      auto OP = operand->get_operand();
      auto dest = Operand(Operand::VREG, temp_reg);
      get_hl_iseq()->append(new Instruction(opcode, dest, OP));

      //Make sure to annotate node with operand
      n->set_operand(dest);

      break;
    }
    case TOK_AMPERSAND: {
      //No code emitted, simply create Operand and save it in node
      //Address of -> convert lval into pointer (vrN) -> vrN
      auto base_reg = operand->get_operand().get_base_reg();
      auto dest = Operand(Operand::VREG, base_reg);
      n->set_operand(dest);
      break;
    }
    case TOK_ASTERISK: {
      //No code emitted, simply create Operand and save it in node
      //dereference -> convert pointer into lval vrN -> (vrN)
      Operand dest;
      if(operand->get_operand().get_kind() == Operand::VREG) {
        dest = operand->get_operand().to_memref();
      }
      else {
        //If kind already == VREG_MEM
        opcode = HINS_mov_q;
        temp_reg = vregAlloc->alloc_temp();
        //Use operand in codegen
        auto OP = operand->get_operand();
        dest = Operand(Operand::VREG, temp_reg);
        get_hl_iseq()->append(new Instruction(opcode, dest, OP));

        //Make sure to annotate node with operand
        dest = dest.to_memref();
      }
      n->set_operand(dest);
      break;
    }
    default: {
      break;
    }
  }
}

void HighLevelCodegen::visit_function_call_expression(Node *n) {
  //printf("FUNCTION CALL \n");
  //Function call expr should:
  //1. Emit mov instructions ->
  //    - For each argument -> move base_reg of operand into argument reg
  //2. Emit Call instruction
  //3. Allocate Temp Reg for the result, store in Operand in Node.
  //4. Emit mov instruction ->
  //    - Move value from vr0 to allocated temp var
  auto varref = n->get_kid(0);
  auto func = varref->get_symbol_ptr();
  auto name = func->get_name();

  visit(varref); //should annotate varref node with operand

  //Emit mov instructions ->
  auto arg_list = n->get_kid(1);
  auto arg_reg_num = 1;
  for(auto i = 0U; i < arg_list->get_num_kids(); i++) {
    auto argument = arg_list->get_kid(i);
    assert(arg_reg_num <= 9);
    //get code for argument
    visit(argument);
    //extract operand
    auto op = argument->get_operand();
    if(argument->get_type()->is_array()) {
      op = Operand(Operand::VREG, op.get_base_reg());
    }
    //Create operand for argument register
    auto dest = Operand(Operand::VREG, arg_reg_num);
    //Create opcode, suffix found from type of argument
    HighLevelOpcode opcode;
    if(argument->get_type()->is_integral()) {
      opcode = get_opcode(HINS_mov_b, argument->get_type());
    }
    else {
      //When parameter type is not integral we are either:
      //Dealing with a pointer, a struct, or an array
      //MOV instructions for all these are suffix with Q as we are dealing with
      //Memory locations
      opcode = HINS_mov_q;
    }
    //Emit mov instruction using operands and opcode.
    get_hl_iseq()->append(new Instruction(opcode, dest, op ));
    //increment the arg_reg counter.
    arg_reg_num++;
  }
  //Emit call instruction
  auto operand = Operand(Operand::LABEL, name);
  auto func_call = new Instruction(HINS_call, operand);
  func_call->set_symbol(func);
  get_hl_iseq()->append(func_call);

  //Allocate temp reg for result
  auto vregAlloc = m_function->get_vregAlloc();
  auto temp_reg = vregAlloc->alloc_temp();

  Operand src_op;
  Operand dest_op = Operand(Operand::VREG, LocalStorageAllocation::VREG_RETVAL);
  //Emit MOV instruction from VREG_RETVAL to temp_reg.
  if(func->get_type()->get_base_type()->get_basic_type_kind() != BasicTypeKind::VOID) {
    auto opcode = get_opcode(HINS_mov_b, func->get_type()->get_base_type());
    dest_op = Operand(Operand::VREG, temp_reg);
    src_op = Operand(Operand::VREG, LocalStorageAllocation::VREG_RETVAL);
    get_hl_iseq()->append(new Instruction(opcode, dest_op,src_op));
  }

  //Annotate node with temp_reg operand
  //Create operand for the result register
  n->set_operand(dest_op);
}

void HighLevelCodegen::visit_field_ref_expression(Node *n) {
  auto VregAlloc = m_function->get_vregAlloc();
  //Available:
  // - VREG_MEM operand from child(0) -> variable ref
  // - name from child(1) -> TOK_ident

  //Should:
  //  - Visit child(0)
  visit(n->get_kid(0));
  auto strct = n->get_kid(0);
  //  - Get structtype from child(0)
  auto type = strct->get_type();
  //  - call get_field_offset() on the structtype using the identifier from child(1)
  auto name = n->get_kid(1)->get_str();
  auto offset = type->get_field_offset(name);
  //  - Allocate temp reg
  auto temp_mov =  VregAlloc->alloc_temp();
  //  - Create operand using temp_reg of type VREG (1)
  auto dest_mov = Operand(Operand::VREG,temp_mov);
  //  - Create Operand using get_field_offset() value of type IMM_VAL (2)
  auto offset_op = Operand(Operand::IMM_IVAL, offset);
  //  - EMIT MOV instruction using (1) as destination and (2) as source.
  auto opcode_mov = HINS_mov_q; //ALWAYS SUFFIX Q AS WE ARE MOVING ADDRESSES
  get_hl_iseq()->append(new Instruction(opcode_mov, dest_mov, offset_op));
  //  - Allocate temp reg
  auto temp_add =  VregAlloc->alloc_temp();
  //  - Create operand using temp_reg of type VREG (3)
  auto dest_add = Operand(Operand::VREG,temp_add);
  //  - Create operand from operand of child(0), but as VREG (4)
  auto base_op = strct->get_operand();
  auto base_reg = base_op.get_base_reg();
  auto base_add = Operand(Operand::VREG, base_reg);
  //  - Emit ADD instruction using (3) as destination, (4) as source and (2) as source.
  auto opcode_add = HINS_add_q; //ALWAYS SUFFIX Q AS WE ARE MOVING ADDRESSES
  get_hl_iseq()->append(new Instruction(opcode_add, dest_add, base_add, dest_mov));
  //  - Create operand of type VREG_MEM (which is otherwise a copy of (3))
  Operand OP_FINAL;
  if(n->get_type()->is_pointer()) {
    OP_FINAL = dest_add;
  }
  else {
    OP_FINAL = dest_add.to_memref();
  }
  //  - Store operand in node.
  n->set_operand(OP_FINAL);
}

void HighLevelCodegen::visit_indirect_field_ref_expression(Node *n) {
  auto VregAlloc = m_function->get_vregAlloc();
  //Available:
  // - VREG_MEM operand from child(0) -> variable ref
  // - name from child(1) -> TOK_ident

  //Should:
  //  - Visit child(0)
  visit(n->get_kid(0));
  //  - Get structtype from child(0)
  auto type = n->get_kid(0)->get_type()->get_base_type();
  //  - call get_field_offset() on the structtype using the identifier from child(1)
  auto name = n->get_kid(1)->get_str();
  auto offset = type->get_field_offset(name);
  //  - Allocate temp reg
  auto temp_mov =  VregAlloc->alloc_temp();
  //  - Create operand using temp_reg of type VREG (1)
  auto dest_mov = Operand(Operand::VREG,temp_mov);
  //  - Create Operand using get_field_offset() value of type IMM_VAL (2)
  auto offset_op = Operand(Operand::IMM_IVAL, offset);
  //  - EMIT MOV instruction using (1) as destination and (2) as source.
  auto opcode_mov = HINS_mov_q; //ALWAYS SUFFIX Q AS WE ARE MOVING ADDRESSES
  get_hl_iseq()->append(new Instruction(opcode_mov, dest_mov, offset_op));
  //  - Allocate temp reg
  auto temp_add =  VregAlloc->alloc_temp();
  //  - Create operand using temp_reg of type VREG (3)
  auto dest_add = Operand(Operand::VREG,temp_add);
  //  - Create operand from operand of child(0), but as VREG (4)
  auto base_reg = n->get_kid(0)->get_operand().get_base_reg();
  auto base_add = Operand(Operand::VREG, base_reg);
  //  - Emit ADD instruction using (3) as destination, (4) as source and (2) as source.
  auto opcode_add = HINS_add_q; //ALWAYS SUFFIX Q AS WE ARE MOVING ADDRESSES
  get_hl_iseq()->append(new Instruction(opcode_add, dest_add, base_add, dest_mov));
  //  - Create operand of type VREG_MEM (which is otherwise a copy of (3))
  Operand OP_FINAL;
  if(n->get_type()->is_pointer()) {
    OP_FINAL = dest_add;
  }
  else {
    OP_FINAL = dest_add.to_memref();
  }
  //  - Store operand in node.
  n->set_operand(OP_FINAL);
}

void HighLevelCodegen::visit_array_element_ref_expression(Node *n) {
  // Available:
  //  - VREG_MEM operand from child 0 -> variable ref
  //  - VREG operand from child 1 -> Literal value

  // Goal: Create operand containing VREG_MEM pointing to correct address of element in mem

  // Do:
  // 1. Visit children
  // 2. Emit mul instruction
  //    - Multiply index with element size
  //    - Store in Temp reg (1)
  // 3. Emit add instruction
  //    - add (1) to base_reg of array
  //    - store in temp_reg of type VREG_MEM (2)
  // 4. Annotate node with (2).

  auto VregAlloc = m_function->get_vregAlloc();

  auto arr = n->get_kid(0);
  auto index = n->get_kid(1);

  //STEP 1: VISIT CHILDREN
  visit(arr);
  visit(index);

  //STEP 2: EMIT MUL INSTRUCTION
  //Get operands for mul instruction
  auto index_op = index->get_operand();
  auto element_size = arr->get_type()->get_base_type()->get_storage_size();
  auto size_op = Operand(Operand::IMM_IVAL, element_size);

  //Allocate temp_reg, get dest operand
  auto temp_reg1 = VregAlloc->alloc_temp();
  auto dest_op_mul = Operand(Operand::VREG, temp_reg1);
  //Emit mul_q instruction (always q suffix as we are dealing with addresses -> 8 byte values)
  get_hl_iseq()->append(new Instruction(HINS_mul_q, dest_op_mul, index_op, size_op));

  //STEP 3: EMIT ADD INSTRUCTION
  //Get operand holding the base address of the array
  auto arr_base_reg = arr->get_operand().get_base_reg();
  auto base_op = Operand(Operand::VREG, arr_base_reg);
  //Allocate temporary register for the result
  auto temp_reg2 = VregAlloc->alloc_temp();
  auto dest_op_add = Operand(Operand::VREG, temp_reg2);
  //Emit add_q instruction (always q suffix as we are dealing with addresses -> 8byte values)
  //Effectively adds the offset from base reg where element is to base reg -> yielding the element address
  get_hl_iseq()->append(new Instruction(HINS_add_q, dest_op_add, base_op, dest_op_mul));

  //STEP 4: Annotate node
  //Create new operand of type VREG_MEM with base reg of dest_op_add
  auto final_op = dest_op_add.to_memref();
  n->set_operand(final_op);
}

void HighLevelCodegen::visit_variable_ref(Node *n)   {
  // Visit variable ref should:
  // If variable ref is taken/array/struct
  //    -> Emit localaddr instruction using symbol Operand
  //    -> Store Operand in node
  // If variable in vreg
  //    -> get Operand from Symbol
  //    -> Store operand in node

  //IMPORTANT DECISION:
  //Note that for variable references into memory a temp vreg
  //has already been allocated during local_storage_allocation
  //Hence allocating a temporary register here is not needed
  //printf("VISIT VAR REF\n");
  auto symbol = n->get_symbol_ptr();
  auto operand = symbol->get_Operand();

  if(operand.get_kind() == Operand::VREG) {
    //For variables with storage in virtual registers
    n->set_operand(operand);
  }
  else if (operand.get_kind() == Operand::VREG_MEM) {
    //For variables with storage in memory
    auto base_reg = m_function->get_vregAlloc()->alloc_temp();
    auto offset = n->get_symbol_ptr()->get_mem_loc();
    //Create operands used for instruction
    auto dest_reg = Operand(Operand::VREG, base_reg);
    auto loc = Operand(Operand::IMM_IVAL, offset);
    //Emit instruction
    get_hl_iseq()->append(new Instruction(HINS_localaddr, dest_reg, loc));
    //this node should be annotated with operand
    //Override n operand with new operand which contains right base reg
    n->set_operand(dest_reg.to_memref());
  }
}

void HighLevelCodegen::visit_literal_value(Node *n) {
  // A partial implementation (note that this won't work correctly
  // for string constants!):

  auto VregAlloc = m_function->get_vregAlloc();

  LiteralValue val = n->get_litval();
  //Based on the type of litval we need to:
  //  TOK_STR_LIT   :
  //      1. Need to Allocate temp Var of type VREG
  //      2. Need to create Operand of type VREG for temp Var
  //      3. Need to find str label
  //      4. Need to create Operand OP of type IMM_LABEL using str_label
  //      5. Need to Emit MOV VR_TEMP OP
  //  TOK_CHAR_LIT  :
  //      1. Need to Allocate temp Var
  //      2. Need to create Operand of type VREG for temp Var
  //      3. Need to create Operand of type IMM_IVAL with ival = LiteralValue.get_int_value()
  //      4. Need to Emit MOV DEST LITVAL
  //  TOK_INT_LIT   :
  //      1. Same as TOK_CHAR_LIT
  //      2. MOV INSTRUCTION TYPE NEEDS TO BE DIFFERENT, USE get_opcode to merge solutions

  int vreg = VregAlloc->alloc_temp();
  Operand dest(Operand::VREG, vreg);

  if(val.get_kind() == LiteralValueKind::STRING) {
    //Find str label
    auto str_label = n->get_string();
    auto OP = Operand(Operand::IMM_LABEL, str_label);
    auto mov_opcode = HINS_mov_q; //Should always be suffix q as we need 8 byte for pointer
    get_hl_iseq()->append(new Instruction(mov_opcode, dest, OP));
    n->set_operand(dest);
  }
  else if (val.get_kind() == LiteralValueKind::INTEGER){
    HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, n->get_type());
    get_hl_iseq()->append(new Instruction(mov_opcode, dest, Operand(Operand::IMM_IVAL, val.get_int_value())));
    n->set_operand(dest);
  }
  else {
    HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, n->get_type());
    get_hl_iseq()->append(new Instruction(mov_opcode, dest, Operand(Operand::IMM_IVAL, val.get_char_value())));
    n->set_operand(dest);
  }
}

void HighLevelCodegen::visit_implicit_conversion(Node *n) {
  //printf("IMPLICIT CONVERSION\n");
  //should allocate temp register
  //should emit sconv / uconv instruction based on type of node
  //should use suffix based on type of child and type of node itself

  visit(n->get_kid(0));

  //DECIDE TO USE sconv or uconv instruction:
  auto isSigned = n->get_type()->is_signed();
  //Decide suffix:
  auto old_type = n->get_kid(0)->get_type()->get_basic_type_kind();
  auto new_type = n->get_type()->get_basic_type_kind();

  HighLevelOpcode opcode;

  if(old_type >= new_type) {
    n->set_operand(n->get_kid(0)->get_operand());
    return;
  }

  //Use iSsigned and typing to get opcode:
  if(isSigned) {
    switch(old_type) {
      case BasicTypeKind::INT: {
        if(new_type == BasicTypeKind::LONG) {
          opcode = HINS_sconv_lq;
        }
        break;
      }
      case BasicTypeKind::SHORT: {
        if(new_type == BasicTypeKind::INT) {
          opcode = HINS_sconv_wl;
        }
        else if(new_type == BasicTypeKind::LONG) {
          opcode = HINS_sconv_wq;
        }
        break;
      }
      case BasicTypeKind::CHAR:{
        if(new_type == BasicTypeKind::INT) {
          opcode = HINS_sconv_bl;
        }
        else if(new_type == BasicTypeKind::SHORT) {
          opcode = HINS_sconv_bw;
        }
        else if(new_type == BasicTypeKind::LONG) {
          opcode = HINS_sconv_bq;
        }
        break;
      }
      case BasicTypeKind::LONG: {
        //LONG are 8 byte -> can never be promoted
        //This should never be visited
        break;
      }
      default: {
        break;
      }
    }
  }
  else {
    switch(old_type) {
      case BasicTypeKind::INT: {
        if(new_type == BasicTypeKind::LONG) {
          opcode = HINS_uconv_lq;
        }
        break;
      }
      case BasicTypeKind::SHORT: {
        if(new_type == BasicTypeKind::INT) {
          opcode = HINS_uconv_wl;
        }
        else if(new_type == BasicTypeKind::LONG) {
          opcode = HINS_uconv_wq;
        }
        break;
      }
      case BasicTypeKind::CHAR:{
        if(new_type == BasicTypeKind::INT) {
          opcode = HINS_uconv_bl;
        }
        else if(new_type == BasicTypeKind::SHORT) {
          opcode = HINS_uconv_bw;
        }
        else if(new_type == BasicTypeKind::LONG) {
          opcode = HINS_uconv_bq;
        }
        break;
      }
      case BasicTypeKind::LONG: {
        //LONG are 8 byte -> can never be promoted
        //This should never be visited
        break;
      }
      default: {
        break;
      }
    }
  }

  //allocate temp register
  auto VregAlloc = m_function->get_vregAlloc();
  auto temp_reg = VregAlloc->alloc_temp();

  //Get operands
  auto dest_op = Operand(Operand::VREG, temp_reg);
  auto src_op = n->get_kid(0)->get_operand();

  //Emit instruction
  get_hl_iseq()->append(new Instruction(opcode, dest_op, src_op));

  //Annotate node with dest operand
  n->set_operand(dest_op);
}

std::string HighLevelCodegen::next_label() {
  std::string label = ".L" + std::to_string(m_next_label_num++);
  return label;
}

// TODO: additional private member functions
