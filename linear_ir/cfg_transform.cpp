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
#include "cfg.h"
#include "cfg_transform.h"

#include "lowlevel.h"

ControlFlowGraphTransform::ControlFlowGraphTransform(std::shared_ptr<ControlFlowGraph> cfg)
  : m_cfg(cfg) {
}

ControlFlowGraphTransform::~ControlFlowGraphTransform() {
}

std::shared_ptr<ControlFlowGraph> ControlFlowGraphTransform::get_orig_cfg() {
  return m_cfg;
}

std::shared_ptr<ControlFlowGraph> ControlFlowGraphTransform::transform_cfg() {
  std::shared_ptr<ControlFlowGraph> result(new ControlFlowGraph());

  // map of basic blocks of original CFG to basic blocks in transformed CFG
  std::map<std::shared_ptr<InstructionSequence>, std::shared_ptr<InstructionSequence>> block_map;

  // iterate over all basic blocks, transforming each one
  for (auto i = m_cfg->bb_begin(); i != m_cfg->bb_end(); i++) {
    std::shared_ptr<InstructionSequence> orig = *i;

    // Transform the instructions
    std::shared_ptr<InstructionSequence> result_bb = transform_basic_block(orig);

    // Set basic block properties (code order, block label, etc.) of result
    // basic block to be the same as the original
    result_bb->set_kind(orig->get_kind());
    result_bb->set_code_order(orig->get_code_order());
    result_bb->set_block_label(orig->get_block_label());

    // Map original block to transformed block
    // (so that we can reconstruct edges)
    block_map[orig] = result_bb;

    // Have CFG formally adopt the basic block
    result->adopt_basic_block(result_bb);
  }

  // add edges to transformed CFG
  for (auto i = m_cfg->bb_begin(); i != m_cfg->bb_end(); i++) {
    std::shared_ptr<InstructionSequence> orig = *i;
    const ControlFlowGraph::EdgeList &outgoing_edges = m_cfg->get_outgoing_edges(orig);
    for (auto j = outgoing_edges.cbegin(); j != outgoing_edges.cend(); j++) {
      Edge *orig_edge = *j;

      std::shared_ptr<InstructionSequence> transformed_source = block_map[orig_edge->get_source()];
      std::shared_ptr<InstructionSequence> transformed_target = block_map[orig_edge->get_target()];

      result->create_edge(transformed_source, transformed_target, orig_edge->get_kind());
    }
  }

  return result;
}

// ----------------------------------------- FUNCTIONS FOR THE LVN SUBCLASS ------------------------------------------

LVNOptimization::LVNOptimization(std::shared_ptr<ControlFlowGraph> cfg)
  : ControlFlowGraphTransform(cfg)
  , m_live_vregs(cfg) {
  m_live_vregs.execute();
}

LVNOptimization::~LVNOptimization() {
}

std::shared_ptr<InstructionSequence>
  LVNOptimization::transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb) {

  struct LVN_key {
    int OPERATION;    // OPERATION = OPCODE
    int LEFTVAL;      // FIRST OPERAND      (-1 IF UNUSED)
    int RIGHTVAL;     // SECOND OPERAND     (-1 IF UNUSED)

    // Define the less-than operator
    bool operator<(const LVN_key& other) const {
      if (OPERATION != other.OPERATION) {
        return OPERATION < other.OPERATION;
      }
      if (LEFTVAL != other.LEFTVAL) {
        return LEFTVAL < other.LEFTVAL;
      }
      return RIGHTVAL < other.RIGHTVAL;
    };
  };

  std::shared_ptr<InstructionSequence> result_iseq = std::make_shared<InstructionSequence>();

  std::map<int, int> CONST_TO_VAL_MAP;               // Map of constant values to their value numbers
  std::map<int, int> VAL_TO_CONST_MAP;               // Map of value numbers to constant values
  std::map<int, int> VREG_TO_VAL_MAP;                // Map of VREG to value numbers
  std::map<int, std::vector<int>> VAL_TO_VREG_MAP;   // Map of Value numbers to set of registers
  std::map<LVN_key, int> KEY_MAP;                    // Map of LVNKEYs to value numbers
  int ValueNumberNext = 0;                           // Next value to be assigned

  for (auto i = orig_bb->cbegin(); i != orig_bb->cend(); ++i) {
    Instruction *orig_ins = *i;
    bool preserve_instruction = true;
    Operand OP_SOURCE[2];
    HighLevelOpcode Opcode;

    LVN_key key;
    key.OPERATION = orig_ins->get_opcode();
    key.LEFTVAL = -1;
    key.RIGHTVAL = -1;

    // For local value numbering we only care about def instructions
    // These are instructions which write something into a register
    // We want to make sure that our transformation is correct, to do so we acknowledge:
    //1. When loading a value from memory (eg. using (v10)) we cannot ensure that it is correct
    //   As such we CANNOT assign this register a number
    //2. Only instructions which copy (eg MOV) or arithmetic instructions are of use
    if (HighLevel::is_def(orig_ins) and orig_ins->get_opcode() != HINS_call) {
      // HANDLE COPYING INSTRUCTIONS (MOV)
      if((key.OPERATION == HINS_mov_b) || (key.OPERATION == HINS_mov_q) || (key.OPERATION == HINS_mov_w) || (key.OPERATION == HINS_mov_l)) {

        auto op0 = orig_ins->get_operand(0);
        auto op1 = orig_ins->get_operand(1);
        int op1_LVN;

        // ------------------- HANDLE OP1 -------------------------------------
        if(op1.is_imm_ival()) {
          auto IMM_VAL = op1.get_imm_ival();
          // IF op1 (the source reg) IS AN IMM VAL, THEN:
          // 1. Check if IMM val already has a local value number
          //    YES : DO NOTHING
          //    NO  : Assign Local value number to IMM val. Update both MAPS.
          if(!CONST_TO_VAL_MAP.contains(IMM_VAL)) {
            CONST_TO_VAL_MAP[IMM_VAL] = ValueNumberNext;
            VAL_TO_CONST_MAP[ValueNumberNext] = IMM_VAL;
            op1_LVN = ValueNumberNext;
            ValueNumberNext++;
          }
          else {
            // Assign Local value number to IMM val. Update both MAPS.
            CONST_TO_VAL_MAP[IMM_VAL] = ValueNumberNext;
            VAL_TO_CONST_MAP[ValueNumberNext] = IMM_VAL;
            op1_LVN = ValueNumberNext;
            ValueNumberNext++;
          }
        }
        else if((!op1.is_non_reg()) and (!op1.is_memref())) {
          auto VREG_NUM = op1.get_base_reg();
          // IF op1 (the source reg) IS AN VREG, THEN:
          // 1. CHECK IF THAT VREG already has a local value number
          //    YES : DO NOTHING
          //    NO  : ASSIGN NEW LVN, UPDATE MAPS
          if(not VREG_TO_VAL_MAP.contains(VREG_NUM)) {
            VREG_TO_VAL_MAP[VREG_NUM] = ValueNumberNext;
            op1_LVN = ValueNumberNext;
            if(VAL_TO_VREG_MAP.contains(ValueNumberNext)) {
              VAL_TO_VREG_MAP[ValueNumberNext].push_back(VREG_NUM);
            }
            else {
              VAL_TO_VREG_MAP[ValueNumberNext] = {VREG_NUM};
            }
            ValueNumberNext++;
          }
        }

        // ------------------- HANDLE OP0 -------------------------------------
        // We are copying into OP0. This means that OP0 Should get the LVN of OP1.
        // We need to update our maps accordingly. If it had a former LVN this entry must be deleted.

        if((!op0.is_non_reg()) and (!op0.is_memref())) { //op0 should just be an ordinary register
          auto VREG_NUM = op0.get_base_reg();
          if(VREG_TO_VAL_MAP.contains(VREG_NUM)) { // If already assigned LVN, remove these from the Maps
            VREG_TO_VAL_MAP.erase(VREG_NUM);
            removeValueFromVecInMap(VAL_TO_VREG_MAP,VREG_NUM);
          }
          // Add the new LVN associations to the maps
          VREG_TO_VAL_MAP[VREG_NUM] = op1_LVN;
          VAL_TO_VREG_MAP[op1_LVN].push_back(VREG_NUM);
        }
      }

      // HANDLE ARITHMETIC INSTRUCTIONS (ALL 3 OPERAND INSTRUCTIONS DEFINED IN HIGH_LEVEL_CODEGEN)
      if((key.OPERATION >= 1) and (key.OPERATION <= 60) ) {
        auto ignore = false;
        auto op2 = orig_ins->get_operand(2);
        auto op1 = orig_ins->get_operand(1);
        auto op0 = orig_ins->get_operand(0);

        // ---------------------- CREATE THE KEY --------------------------
        // STEP 1: GET OPERAND 2 LVN

        if(op2.is_imm_ival()) {
          auto IMM_VAL = op2.get_imm_ival();
          //Check if IMM_IVAL already has LVN
          if(CONST_TO_VAL_MAP.contains(IMM_VAL)) {
            key.RIGHTVAL = CONST_TO_VAL_MAP[IMM_VAL];
          }
          else{
            CONST_TO_VAL_MAP[IMM_VAL] = ValueNumberNext;
            VAL_TO_CONST_MAP[ValueNumberNext] = IMM_VAL;
            key.RIGHTVAL = ValueNumberNext;
            ValueNumberNext++;
          }
        }
        else if((not op2.is_non_reg()) and (not op2.is_memref())) { // NOT IMM VAL, NOT MEMREF -> MUST BE REG
          auto VREG_NUM = op2.get_base_reg();
          if(VREG_TO_VAL_MAP.contains(VREG_NUM)) {
            key.RIGHTVAL = VREG_TO_VAL_MAP[VREG_NUM];
          }
          else {
            VREG_TO_VAL_MAP[VREG_NUM] = ValueNumberNext;
            if(VAL_TO_VREG_MAP.contains(ValueNumberNext)){VAL_TO_VREG_MAP[ValueNumberNext].push_back(VREG_NUM);}
            else{VAL_TO_VREG_MAP[ValueNumberNext] = {VREG_NUM};}
            key.RIGHTVAL = ValueNumberNext;
            ValueNumberNext++;
          }
        }
        else {ignore = true;}

        // STEP 2: GET OPERAND 1 LVN
        if(op1.is_imm_ival()) {
          auto IMM_VAL = op1.get_imm_ival();
          //Check if IMM_IVAL already has LVN
          if(CONST_TO_VAL_MAP.contains(IMM_VAL)) {
            key.LEFTVAL = CONST_TO_VAL_MAP[IMM_VAL];
          }
          else {
            CONST_TO_VAL_MAP[IMM_VAL] = ValueNumberNext;
            VAL_TO_CONST_MAP[ValueNumberNext] = IMM_VAL;
            key.LEFTVAL = ValueNumberNext;
            ValueNumberNext++;
          }
        }
        else if((not op1.is_non_reg()) and (not op1.is_memref())) { // NOT IMM VAL, NOT MEMREF -> MUST BE REG
          auto VREG_NUM = op1.get_base_reg();
          if(VREG_TO_VAL_MAP.contains(VREG_NUM)) {
            key.LEFTVAL = VREG_TO_VAL_MAP[VREG_NUM];
          }
          else {
            VREG_TO_VAL_MAP[VREG_NUM] = ValueNumberNext;
            if(VAL_TO_VREG_MAP.contains(ValueNumberNext)){VAL_TO_VREG_MAP[ValueNumberNext].push_back(VREG_NUM);}
            else{VAL_TO_VREG_MAP[ValueNumberNext] = {VREG_NUM};}
            key.LEFTVAL = ValueNumberNext;
            ValueNumberNext++;
          }
        }
        else {ignore = true;}

        // STEP 3: CHECK IF KEY ALREADY IN MAP
        if(KEY_MAP.contains(key) && !ignore) { // YES
          auto VREG_NUM = op0.get_base_reg();
          // UPDATE op0 LVN TO BE FOUND LVN, update MAPS
          if(VREG_TO_VAL_MAP.contains(VREG_NUM)) { // If already assigned LVN, remove these from the Maps
            VREG_TO_VAL_MAP.erase(VREG_NUM);
            removeValueFromVecInMap(VAL_TO_VREG_MAP,VREG_NUM);
          }
          // Add the new LVN associations to the maps
          VREG_TO_VAL_MAP[VREG_NUM] = KEY_MAP[key];
          VAL_TO_VREG_MAP[KEY_MAP[key]].push_back(VREG_NUM);

          // REPLACE INSTRUCTION WITH MOV
          preserve_instruction = false;
          OP_SOURCE[0] = op0;
          OP_SOURCE[1] = Operand(Operand::VREG, VAL_TO_VREG_MAP[KEY_MAP[key]][0]);
          switch(key.OPERATION % 4) {
            case 1: { Opcode = HINS_mov_b; break; }
            case 2: { Opcode = HINS_mov_w; break; }
            case 3: { Opcode = HINS_mov_l; break; }
            case 0: { Opcode = HINS_mov_q; break; }
            default: break;
          }
        }
        else { // KEY NOT IN MAP
          auto VREG_NUM = op0.get_base_reg();
          // CREATE NEW LVN, UPDATE MAPS
          if(!ignore) {
            KEY_MAP[key] = ValueNumberNext;
            //printf("KEY CREATED: %d, %d, %d \n", key.OPERATION, key.LEFTVAL, key.RIGHTVAL);
          } //only want to add new key if not ignore
          // ASSIGN op0 VREG LVN, UPDATE MAPS.        //Still want to remove/update other maps
          VREG_TO_VAL_MAP[VREG_NUM] = ValueNumberNext;
          VAL_TO_VREG_MAP[ValueNumberNext] = {VREG_NUM}; // Should be a new LVN, so should never push back
          ValueNumberNext++;
        }
      }

      // HANDLE SCONV AND UCONV INSTRUCTIONS, AND LOCALADDR INSTRUCTIONS
      // We dont want to change these instructions, but we want to make keys such that we can
      // use the associations for further simplifying
      if(((key.OPERATION >= 97) and (key.OPERATION <= 108)) or (key.OPERATION == 114)) {
        auto ignore = false;
        auto op1 = orig_ins->get_operand(1);
        auto op0 = orig_ins->get_operand(0);

        // ---------------------- CREATE THE KEY --------------------------
        key.RIGHTVAL = -1;

        // STEP 1: GET SOURCE OPERAND LVN
        if(op1.is_imm_ival()) {
          auto IMM_VAL = op1.get_imm_ival();
          //Check if IMM_IVAL already has LVN
          if(CONST_TO_VAL_MAP.contains(IMM_VAL)) {
            key.LEFTVAL = CONST_TO_VAL_MAP[IMM_VAL];
          }
          else {
            CONST_TO_VAL_MAP[IMM_VAL] = ValueNumberNext;
            VAL_TO_CONST_MAP[ValueNumberNext] = IMM_VAL;
            key.LEFTVAL = ValueNumberNext;
            ValueNumberNext++;
          }
        }
        else if((not op1.is_non_reg()) and (not op1.is_memref())) { // NOT IMM VAL, NOT MEMREF -> MUST BE REG
          auto VREG_NUM = op1.get_base_reg();
          if(VREG_TO_VAL_MAP.contains(VREG_NUM)) {
            key.LEFTVAL = VREG_TO_VAL_MAP[VREG_NUM];
          }
          else {
            VREG_TO_VAL_MAP[VREG_NUM] = ValueNumberNext;
            VAL_TO_VREG_MAP[ValueNumberNext] = {VREG_NUM};
            key.LEFTVAL = ValueNumberNext;
            ValueNumberNext++;
          }
        }
        else{ignore = true;}

      // STEP 2: CHECK IF KEY ALREADY IN MAP
        if(KEY_MAP.contains(key) && !ignore) { // YES
          auto VREG_NUM = op0.get_base_reg();
          // UPDATE op0 LVN TO BE FOUND LVN, update MAPS
          if(VREG_TO_VAL_MAP.contains(VREG_NUM)) { // If already assigned LVN, remove these from the Maps
            VREG_TO_VAL_MAP.erase(VREG_NUM);
            removeValueFromVecInMap(VAL_TO_VREG_MAP,VREG_NUM);
          }
          // Add the new LVN associations to the maps
          VREG_TO_VAL_MAP[VREG_NUM] = KEY_MAP[key];
          VAL_TO_VREG_MAP[KEY_MAP[key]].push_back(VREG_NUM);

          // REPLACE INSTRUCTION WITH MOV
          preserve_instruction = false;
          OP_SOURCE[0] = op0;
          OP_SOURCE[1] = Operand(Operand::VREG, VAL_TO_VREG_MAP[KEY_MAP[key]][0]);
          auto size = highlevel_opcode_get_dest_operand_size(HighLevelOpcode(key.OPERATION));
          switch(size) {
            case 1: { Opcode = HINS_mov_b; break; } // SHOULD NOT HAPPEN
            case 2: { Opcode = HINS_mov_w; break; } // ALL INSTRUCTIONS ENDING IN W
            case 4: { Opcode = HINS_mov_l; break; } // ALL INSTRUCTIONS ENDING IN L
            case 8: { Opcode = HINS_mov_q; break; } // ALL INSTRUCTIONS ENDING IN Q AND LOCALADDR
            default: Opcode = HINS_mov_q;
          }
        }
        else { // KEY NOT IN MAP
          auto VREG_NUM = op0.get_base_reg();
          // CREATE NEW LVN (DEST), UPDATE MAPS
          if(!ignore) {
            //printf("KEY CREATED: %d, %d, %d \n", key.OPERATION, key.LEFTVAL, key.RIGHTVAL);
            KEY_MAP[key] = ValueNumberNext;
          }
          // ASSIGN op0 VREG LVN, UPDATE MAPS.
          VREG_TO_VAL_MAP[VREG_NUM] = ValueNumberNext;
          VAL_TO_VREG_MAP[ValueNumberNext] = {VREG_NUM}; // Should be a new LVN, so should never push back
          ValueNumberNext++;
        }
      }
    }

    //printf("KEY CREATED: %d, %d, %d \n", key.OPERATION, key.LEFTVAL, key.RIGHTVAL);

    //Dont change the instruction
    if (preserve_instruction) { result_iseq->append(orig_ins->duplicate());}
    //Not preserving the instruction
    else {result_iseq->append(new Instruction(Opcode, OP_SOURCE[0], OP_SOURCE[1]));}
  }
  return result_iseq;
}

// ----------------------------------------- FUNCTIONS FOR THE DEAD-STORE SUBCLASS ------------------------------------

DSOptimization::DSOptimization(std::shared_ptr<ControlFlowGraph> cfg)
  : ControlFlowGraphTransform(cfg)
  , m_live_vregs(cfg) {
  m_live_vregs.execute();
}

DSOptimization::~DSOptimization() {
}

std::shared_ptr<InstructionSequence>
  DSOptimization::transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb)
  {
    std::shared_ptr<InstructionSequence> result_iseq =std::make_shared<InstructionSequence>();

    for (auto i = orig_bb->cbegin(); i != orig_bb->cend(); ++i) {
      Instruction *orig_ins = *i;
      bool preserve_instruction = true;

      if (HighLevel::is_def(orig_ins) and (orig_ins->get_opcode() != HINS_call)) {
        Operand dest = orig_ins->get_operand(0);

        LiveVregs::FactType live_after =
          m_live_vregs.get_fact_after_instruction(orig_bb, orig_ins);
        if (!live_after.test(dest.get_base_reg())){
          // destination register is dead immediately after this instruction,
            // so it can be eliminated
            // Dont want to remove special registers (eg. argument and return registers)
            if(dest.get_base_reg() >= 10) preserve_instruction = false;
        }
      }

      auto opcode = orig_ins->get_opcode();
      if(opcode == HINS_mov_b || opcode == HINS_mov_w || opcode == HINS_mov_l|| opcode == HINS_mov_q) {
        auto op0 = orig_ins->get_operand(0);
        auto op1 = orig_ins->get_operand(1);
        if(!op0.is_non_reg() and !op0.is_memref()) {
          if(!op1.is_non_reg() and !op1.is_memref()) {
            if(op1.get_base_reg() == op0.get_base_reg()) {
              preserve_instruction = false;
            }
          }
        }
      }

      if (preserve_instruction)
        result_iseq->append(orig_ins->duplicate());
    }
    return result_iseq;
}

// ----------------------------------------- FUNCTIONS FOR THE COPY-PROPAGATION SUBCLASS -----------------------------

CPOptimization::CPOptimization(std::shared_ptr<ControlFlowGraph> cfg)
  : ControlFlowGraphTransform(cfg)
  , m_live_vregs(cfg) {
  m_live_vregs.execute();
}

CPOptimization::~CPOptimization() {
}

std::shared_ptr<InstructionSequence>
  CPOptimization::transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb) {

  // ALGORITHM:
  // 1. Start from the first instruction in the BB.
  // 2. Whenever we encounter any instruction we:
  //    A) Check if any of the source registers are a key in the map - if so replace it with the associated value
  //    B) Check if the destination register is part of any pair in any map - if so remove the pair from the map.
  // 3. Whenever we encounter a MOV instruction where both operands are registers, we:
  //    A) Add the register pair to a map
  // 4. Whenever we encounter a MOV instruction where the source operand is a Constant, we:
  //    A) Add the register-constant pair to a map


  std::shared_ptr<InstructionSequence> result_iseq =std::make_shared<InstructionSequence>();

  std::map<int,int> VREG_MAP;  // KEYS ARE REGISTERS WHICH CAN BE REPLACED, VALUE IS THE REGISTER BEING PROPAGATED
  std::map<int,int> CONST_MAP; // CONSTANTS TO REGISTERS

  for (auto i = orig_bb->cbegin(); i != orig_bb->cend(); ++i) {
    Instruction *orig_ins = *i;
    bool preserve_instruction = true;
    Operand OP_SOURCE[2];
    Operand dest;
    auto opcode = orig_ins->get_opcode();
    auto num_op = orig_ins->get_num_operands();
    // 2. Whenever we encounter any instruction we:
    //    A) Check if any of the source registers are a key in the map - if so replace it with the associated value
      for(auto i = 1U; i < orig_ins->get_num_operands();i++) {
        auto op = orig_ins->get_operand(i);
        OP_SOURCE[i-1] = op;
        if(!op.is_non_reg() && !op.is_memref()) {
          if(VREG_MAP.contains(op.get_base_reg())) {
            preserve_instruction = false;
            OP_SOURCE[i-1] = Operand(Operand::VREG, VREG_MAP[op.get_base_reg()]);
          }
          if(CONST_MAP.contains(op.get_base_reg())) {
            preserve_instruction = false;
            OP_SOURCE[i-1] = Operand(Operand::IMM_IVAL, CONST_MAP[op.get_base_reg()]);
          }
        }
        else if(op.is_memref()) {
          if(VREG_MAP.contains(op.get_base_reg())) {
            preserve_instruction = false;
            OP_SOURCE[i-1] = Operand(Operand::VREG_MEM, VREG_MAP[op.get_base_reg()]);
          }
        }
      }

      // 2. Whenever we encounter any instruction we:
      //    B) Check if the destination register is part of any pair in the maps - if so remove the pair from the maps.
      if(num_op >= 1) {
        dest = orig_ins->get_operand(0);
        if((!dest.is_non_reg()) and (!dest.is_memref())) {
          removePairsWithValue(VREG_MAP, dest.get_base_reg());
          if(CONST_MAP.contains(dest.get_base_reg())) CONST_MAP.erase(dest.get_base_reg());
        }
      }

      if((opcode== HINS_mov_b) || (opcode == HINS_mov_w) || (opcode == HINS_mov_l) || (opcode == HINS_mov_q)) {
        Operand dest = orig_ins->get_operand(0);
        Operand source = orig_ins->get_operand(1);
        if((!dest.is_non_reg()) and (!dest.is_memref())) {
          if((!source.is_non_reg()) and (!source.is_memref())) {
            // 3. Whenever we encounter a MOV instruction where both operands are registers, we:
            //    A) Add the register pair to a map
            auto VREG_DEST = dest.get_base_reg();
            auto VREG_SOURCE = source.get_base_reg();
            VREG_MAP[VREG_DEST] = VREG_SOURCE;
          }
          else if (source.is_imm_ival()) {
            // 4. Whenever we encounter a MOV instruction where the source operand is a Constant, we:
            //    A) Add the register-constant pair to a map
            auto VREG_DEST = dest.get_base_reg();
            auto IMM_SOURCE = source.get_imm_ival();
            CONST_MAP[VREG_DEST] = IMM_SOURCE;
          }
        }
      }

    if (preserve_instruction) {
      result_iseq->append(orig_ins->duplicate());
    }
    else {
      if(num_op == 0) {result_iseq->append(new Instruction(opcode));}
      if(num_op == 1) {result_iseq->append(new Instruction(opcode, dest));}
      if(num_op == 2) {result_iseq->append(new Instruction(opcode, dest, OP_SOURCE[0]));}
      if(num_op  == 3){result_iseq->append(new Instruction(opcode, dest, OP_SOURCE[0],OP_SOURCE[1]));}
    }
  }
  return result_iseq;
}

// Function to remove all occurrences of a value in all vectors in the map
void removeValueFromVecInMap(std::map<int, std::vector<int>>& map, int valueToRemove) {
  for (auto& pair : map) {
    auto& vec = pair.second;

    // Remove all occurrences of valueToRemove from the vector
    vec.erase(std::remove(vec.begin(), vec.end(), valueToRemove), vec.end());
  }
}

void removePairsWithValue(std::map<int, int>& myMap, int valueToRemove) {
  for (auto it = myMap.begin(); it != myMap.end(); ) {
    if (it->second == valueToRemove || it->first == valueToRemove) {
      it = myMap.erase(it);  // erase returns the next iterator
    }
    else {
      ++it;  // only increment if not erasing
    }
  }
}

// Function to find a value in the map and return the first element of the vector
int findValueInMap(const std::map<int, std::vector<int>>& myMap, int valueToFind) {
  for (const auto& pair : myMap) {
    const auto& vec = pair.second;
    if (std::find(vec.begin(), vec.end(), valueToFind) != vec.end()) {
      return vec.front(); // Return the first element of the vector
    }
  }
  return -1; // Sentinel value indicating the value was not found
}

// --------------------------------------- FUNCTIONS FOR THE LOCAL REGISTER ALLOCATION ------------------------

LRAOptimization::LRAOptimization(std::shared_ptr<ControlFlowGraph> cfg, std::shared_ptr<Function> func )
  : ControlFlowGraphTransform(cfg)
  , m_live_vregs(cfg)
  , m_function(func)
  , m_spilledStorage(0){
  m_live_vregs.execute();
}

LRAOptimization::~LRAOptimization() {
}

// STRUCTURE CHANGES NEEDED:
//  1. INSTRUCTIONS NEED ABILITY TO BE ANNOTATED:
//      ADD FIELD TO OPERAND
//      MachineReg m_MachineReg = MachineReg (which low-level should use)
//      (together with opcode the size of machineReg can be derived, therefore not saved)
//  2. LOW-LEVEL CODE NEEDS TO CHOOSE MACHINEREGS WHEN POSSIBLE
//      Alter the LOW-LEVEL code.
//  3. LOW-LEVEL CODE NEEDS TO ALLOCATE SPACE IN STACK FRAME FOR SPILLS
//      Alter the LOW-LEVEL code.
//  4. LOW-LEVEL CODE NEEDS TO BE ABLE TO HANDLE SPILLS
//      Alter the LOW-LEVEL code.
//  5. INSTRUCTIONSEQUENCE NEEDS TO BE ABLE TO HOLD THE MEMORY FOR SPILLS
//      Add Field to INSTRUCTIONSEQUENCE
//      Add Field to CONTROLFLOWGRAPH

std::shared_ptr<InstructionSequence>
  LRAOptimization::transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb) {

  //Algorithm:
  // INITIAL:
  //  1. Check if last instruction is call()
  //     If last instruction is call, add argument registers to reserved list
  //  2. Add all local registers/parameter registers to reserved list
  //  3.

  //  For each instruction:
  //    For each operand (do the dest last):
  //        If operand is register/mem_ref:
  //          If register not in reserved list:
  //            Allocate/assign machineregister (top of machineregQueue / assigned machineregQueue)
  //              If machineregister available take top of machineregQueue
  //              Else steal machinereg and spill the variable previously stored to mem
  //            Annotate Operand with machineregister
  //            if register dead after instruction
  //              Free machinereg

  std::shared_ptr<InstructionSequence> result_iseq = std::make_shared<InstructionSequence>();
  std::deque<int> M_Queue;       //Queue used for MachineRegs
  std::vector<int> reservedList;        //Vector holding all local/param registers. These should be ignored/reserved.
  std::map<int,int> AssignMap;   //Map Holding the assignment of VREGS (key) to MachineRegs (value).
  std::map<int,int> spilledMap;         //Map holding the key-value pairs of registers and locations of spillage.
  int spilled_storage = 0;
  //--------------- FILL THE M_QUEUE ------------------------------------
  for(auto i = 15; i >= 0; i--) M_Queue.push_back(i);
  //--------------- RESERVE MACHINEREGS IF CALL IN BB -------------------
  //--- ORDERED ARGUMENT REGISTERS: %rdi, %rsi, %rdx, %rcx, %r8, and %r9
  if((orig_bb->get_length() != 0) and (orig_bb->get_last_instruction()->get_opcode() == HINS_call)) {
    auto num_args = orig_bb->get_last_instruction()->get_symbol()->get_type()->get_num_members();
    if(num_args >= 1) {removeValueFromDeque(M_Queue, MREG_RDI); num_args--;}
    if(num_args >= 1) {removeValueFromDeque(M_Queue, MREG_RSI); num_args--;}
    if(num_args >= 1) {removeValueFromDeque(M_Queue, MREG_RDX); num_args--;}
    if(num_args >= 1) {removeValueFromDeque(M_Queue, MREG_RCX); num_args--;}
    if(num_args >= 1) {removeValueFromDeque(M_Queue, MREG_R8 ); num_args--;}
    if(num_args >= 1) {removeValueFromDeque(M_Queue, MREG_R9 ); }
  }
  //--------------- REMOVE %R10, %R11, %RSP, %RBP -----------------------
  // Can't use R10 or R11 as these are used for 3-reg instructions/CMPLT
  // Can't use RSP or RBP as these are used for memory addressing
  // Can't use RAX (return value register) as this is used for vr0
  removeValueFromDeque(M_Queue, MREG_R10);
  removeValueFromDeque(M_Queue, MREG_R11);
  removeValueFromDeque(M_Queue, MREG_RSP);
  removeValueFromDeque(M_Queue, MREG_RBP);
  removeValueFromDeque(M_Queue, MREG_RAX);

  //--------------- PUT REGISTERS IN RESERVEDLIST -----------------------
  // The Total register storage (local registers and parameters)
  if(orig_bb->get_length() != 0){
    LiveVregs::FactType live_start = m_live_vregs.get_fact_at_beginning_of_block(orig_bb);
    LiveVregs::FactType live_end = m_live_vregs.get_fact_at_end_of_block(orig_bb);
    for(auto j = 0; j <= 10; j++) reservedList.push_back(j); // VR0-10 ALWAYS RESERVED
    for(auto i = 11; i <= 255; i++) { //Reserve local registers if needed
      if (live_start.test(i)){ // REG i ALIVE IN START OF BB
        reservedList.push_back(i);
      }
      else if(live_end.test(i)) { // REG i ALIVE AT END OF BB
        reservedList.push_back(i);
      }
    }

    /*
    printf("RESERVED REGISTERS: ");
    for( int val : reservedList) {
      printf("%d ", val);
    }
    printf("\n");
    */

  }


  //--------------- ITERATE THROUGH ALL INSTRUCTIONS --------------------
  for (auto i = orig_bb->cbegin(); i != orig_bb->cend(); ++i) {

    Instruction *orig_ins = *i;
    auto opcode = HighLevelOpcode(orig_ins->get_opcode());
    Operand op[3];

    //------------------- COMPUTE OPERANDS -------------------------
    auto num_op = orig_ins->get_num_operands();
    for(auto i = int(num_op-1); i >= 0; i--) { // START WITH SOURCE OPS, DO DEST OP LAST
      op[i] = orig_ins->get_operand(i);

      // ONLY HANDLE MEMREFS AND REGISTERS
      if(!op[i].is_non_reg() && !isValueInVector(reservedList, op[i].get_base_reg())) {
        auto base_reg = op[i].get_base_reg();
        int MR;
        // CHECK IF VREG IS SPILLED - IF SO RESTORE IT TO ALLOCATED MREG
        if(spilledMap.contains(base_reg)) { // YES IT IS SPILLED, ALLOCATE MREG AND RESTORE
          MR = assignMreg(result_iseq, spilledMap, AssignMap, M_Queue,
            spilled_storage, base_reg, m_function);
          restoreVreg(result_iseq, base_reg, MR, opcode, spilledMap); // Restore VREG to Allocated MREG
        }
        // IF VREG NOT SPILLED, CHECK IF IT HAS ASSIGNED MREG
        else if(!AssignMap.contains(base_reg)) { // NO - ASSIGN ONE
          MR = assignMreg(result_iseq, spilledMap, AssignMap, M_Queue,
            spilled_storage, base_reg, m_function);
        }
        else {                                   // YES - SIMPLY COPY
          MR = AssignMap[base_reg];
        }
        //---------------------- ANNOTATE OPERAND -------------------
        op[i].set_MachineReg(MR);
        op[i].set_MRegSize(highlevel_opcode_get_source_operand_size(opcode));
        //------------------- FREE OPERAND IF DEAD ------------------
        LiveVregs::FactType live_after = m_live_vregs.get_fact_after_instruction(orig_bb, orig_ins);
        if (!live_after.test(base_reg)){ // REG NOT ALIVE AFTER INSTRUCTION
          if(AssignMap.contains(base_reg)) { // REG HAS ASSIGNED MREG
            M_Queue.push_front(AssignMap[base_reg]); // PUT MREG BACK IN QUEUE/POOL
            AssignMap.erase(base_reg); // REMOVE KEY-VALUE PAIR FROM ASSIGNMAP (NO LONGER ASSIGNED)
          }
        }
        // IF A SPILLED VREG IS USED AS DEST OPERAND
        // IT SHOULD NO LONGER BE "SPILLED" AS THE SPILLED VALUE WOULD NOW BE GARBAGE
        if(spilledMap.contains(base_reg) && i == 0){spilledMap.erase(base_reg);}
      }
    }

    // EMIT ORIGINAL INSTRUCTION, WITH ANNOTATED OPERANDS
    if(num_op == 3) result_iseq->append(new Instruction(opcode, op[0], op[1],op[2]));
    if(num_op == 2) result_iseq->append(new Instruction(opcode, op[0], op[1]));
    if(num_op == 1) result_iseq->append(new Instruction(opcode, op[0]));
    if(num_op == 0) result_iseq->append(new Instruction(opcode));
  }
  //update the spilled storage
  if(spilled_storage > m_spilledStorage) m_spilledStorage = spilled_storage;
  return result_iseq;
}

// Function to remove all occurrences of a specific value from a deque
void removeValueFromDeque(std::deque<int>& deq, int valueToRemove) {
  // Use std::remove to move the values to be removed to the end of the deque
  auto newEnd = std::remove(deq.begin(), deq.end(), valueToRemove);
  // Erase the "removed" values from the deque
  deq.erase(newEnd, deq.end());
}

// Function to check if a value exists in a vector
bool isValueInVector(const std::vector<int>& vec, int valueToFind) {
  // Use std::find to search for the value
  auto it = std::find(vec.begin(), vec.end(), valueToFind);
  // Return true if the value is found, otherwise false
  return it != vec.end();
}

// This function should:
// 1. Search the result instruction sequence from the top for a VREG in AssignMap
//    It stands to good reason that the first VREG encountered this way is least likely to be used
//    As it was allocated longest ago and therefore least recently used.
// 2. Lookup the Vreg in AssignMap and acquire the Machine reg, then erase the value-pair from AssignMap.
// 3. Update SpilledMap with pair of victimVreg and offset
// 4. Increment spilled_storage
// 5. Emit Spill Instruction, append to result_iseq
// 6. Stolen MREG returned.
int stealMachineReg(std::map<int,int>& AssignMap, std::shared_ptr<InstructionSequence> result_iseq,
                    unsigned offset, std::map<int,int>& spilledMap, int& spilled_storage) {
  int StolenMREG;
  int victimBaseReg = -1;
  int VBRSize = 0;
  Operand SrcOp;
  Operand immOp;
  HighLevelOpcode spill_opcode;

  for (auto i = result_iseq->cbegin(); i != result_iseq->cend(); ++i) {
    auto instr = *i;
    auto opcode = HighLevelOpcode(instr->get_opcode());
    auto num_ops = instr->get_num_operands();

    for(auto j = 0U; j < num_ops; j++) {      // INSTRUCTION WITH 0 OPERANDS WILL BE SKIPPED
      auto op = instr->get_operand(j);
      if(!op.is_non_reg()) {                  // ONLY INTERESTED IN REGISTER OPERANDS
        auto base_reg = op.get_base_reg();
        if(AssignMap.contains(base_reg)) {    // BASE REG WITH ASSIGNED MREG LOCATED. STEAL.
          victimBaseReg = base_reg;
          if(num_ops == 1) { //FOR 1-REG INSTRUCTION THE REG MUST BE DESTINATION REG
            VBRSize = highlevel_opcode_get_dest_operand_size(opcode);
          }
          if(num_ops == 2) { // FOR 2-REG INSTRUCTION FIRST REG IS DEST, SECOND IS SRC
            if(j == 0) VBRSize = highlevel_opcode_get_dest_operand_size(opcode);
            if(j == 1) VBRSize = highlevel_opcode_get_source_operand_size(opcode);
          }
          if(num_ops == 3) { // FOR 3-REG INSTRUCTION FIRST REG IS DEST, SECOND&THIRD IS SRC
            if(j == 0) VBRSize = highlevel_opcode_get_dest_operand_size(opcode);
            if(j == 1) VBRSize = highlevel_opcode_get_source_operand_size(opcode);
            if(j == 2) VBRSize = highlevel_opcode_get_source_operand_size(opcode);
          }
          break;
        }
      }
    }
    if(victimBaseReg != -1) break;
  }

  // GET STOLEN MREG AND UPDATE AssignMAP
  StolenMREG = AssignMap[victimBaseReg];  // GET THE MREG
  AssignMap.erase(victimBaseReg);         // ERASE THE MAP ENTRY

  // ADD victimBaseReg to spilledMap, increment spilled_storage
  spilledMap[victimBaseReg] = offset;
  spilled_storage += VBRSize;

  // EMIT INSTRUCTION
  SrcOp = Operand(Operand::VREG, victimBaseReg);
  SrcOp.set_MachineReg(StolenMREG);
  SrcOp.set_MRegSize(VBRSize);
  immOp = Operand(Operand::IMM_IVAL, offset);
  if(VBRSize == 1) spill_opcode = HINS_spill_b;
  else if(VBRSize == 2) spill_opcode = HINS_spill_w;
  else if(VBRSize == 4) spill_opcode = HINS_spill_l;
  else spill_opcode = HINS_spill_q; //(VBRSize == 8)

  auto spill_instr = new Instruction(spill_opcode, SrcOp, immOp);

  result_iseq->append(spill_instr);

  return StolenMREG;
}

void restoreVreg(std::shared_ptr<InstructionSequence> result_iseq, int base_reg, int MR, HighLevelOpcode opcode, std::map<int,int>& spilledMap) {

  auto destOp = Operand(Operand::VREG,base_reg);
  auto immOp = Operand(Operand::IMM_IVAL, spilledMap[base_reg]);

  destOp.set_MachineReg(MR);  //ANNOTATE VREG WITH MACHINEREG FOR LL-CODE
  destOp.set_MRegSize(highlevel_opcode_get_source_operand_size(opcode));

  // GET RESTORE OPCODE
  auto restore_opcode = HINS_restore_q;
  auto size = highlevel_opcode_get_source_operand_size(opcode);
  if(size == 1) restore_opcode = HINS_restore_b;
  if(size == 2) restore_opcode = HINS_restore_w;
  if(size == 4) restore_opcode = HINS_restore_l;
  if(size == 8) restore_opcode = HINS_restore_q;
  // EMIT INSTRUCTION
  result_iseq->append(new Instruction(restore_opcode, destOp,immOp));
  // REMOVE REG-VALUE PAIR FROM MAP, NO LONGER SPILLED
  spilledMap.erase(base_reg);
}

int assignMreg(std::shared_ptr<InstructionSequence> result_iseq, std::map<int,int>& spilledMap,
               std::map<int,int>& AssignMap, std::deque<int> &M_Queue, int& spilled_storage,
               int base_reg, std::shared_ptr<Function> m_function) {

  int MR;
  if(M_Queue.empty()) {            // NO MREGS AVAILABLE, STEAL ONE, SPILL
    auto offset = m_function->get_total_storage()+spilled_storage;
    MR = stealMachineReg(AssignMap, result_iseq, offset, spilledMap,spilled_storage);
  }
  else {                           // MREG AVAILABLE, ASSIGN IT, REMOVE FROM QUEUE.
    MR = M_Queue.front();
    M_Queue.pop_front();
  }
  AssignMap[base_reg] = MR;       //UPDATE MAP
  return MR;
}
