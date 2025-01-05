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

#ifndef CFG_TRANSFORM_H
#define CFG_TRANSFORM_H

#include <memory>
#include "cfg.h"
#include "function.h"
#include "highlevel.h"
#include "live_vregs.h"

//! Base class for ControlFlowGraphTransform transformations.
//! This is the preferred way to implement local optimizations.
//! In general, implementations of ControlFlowGraphTransform are
//! intended to be nondestructive, meaning that they return a
//! new result ControlFlowGraph without modifying the original one.
class ControlFlowGraphTransform {
private:
  std::shared_ptr<ControlFlowGraph> m_cfg;

public:
  //! Constructor.
  //! @param cfg the ControlFlowGraph to transform
  ControlFlowGraphTransform(std::shared_ptr<ControlFlowGraph> cfg);
  virtual ~ControlFlowGraphTransform();

  //! Get a shared pointer to the original ControlFlowGraph.
  //! @return the original ControlFlowGraph
  std::shared_ptr<ControlFlowGraph> get_orig_cfg();

  //! Transform the original ControlFlowGraph.
  //! @return shared pointer to the transformed ControlFlowGraph
  virtual std::shared_ptr<ControlFlowGraph> transform_cfg();

  //! Create a transformed version of the instructions in a basic block.
  //! Note that an InstructionSequence "owns" the Instruction objects it contains,
  //! and is responsible for deleting them. Therefore, be careful to avoid
  //! having two InstructionSequences contain pointers to the same Instruction.
  //! If you need to make an exact copy of an Instruction object, you can
  //! do so using the `duplicate()` member function, as follows:
  //!
  //! ```
  //! Instruction *orig_ins = // ...an Instruction object...
  //! Instruction *dup_ins = orig_ins->duplicate();
  //! ```
  //!
  //! @param orig_bb the original basic block
  //! @return shared pointer to the new basic block InstructionSequence
  virtual std::shared_ptr<InstructionSequence> transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb) = 0;
};

class LVNOptimization : public ControlFlowGraphTransform {
private:
  LiveVregs m_live_vregs;

public:
  LVNOptimization(std::shared_ptr<ControlFlowGraph> cfg);
  ~LVNOptimization();

  virtual std::shared_ptr<InstructionSequence>
    transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb);
};

class DSOptimization : public ControlFlowGraphTransform {
private:
  LiveVregs m_live_vregs;

public:
  DSOptimization(std::shared_ptr<ControlFlowGraph> cfg);
  ~DSOptimization();

  virtual std::shared_ptr<InstructionSequence>
    transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb);
};

class CPOptimization : public ControlFlowGraphTransform {
private:
  LiveVregs m_live_vregs;

public:
  CPOptimization(std::shared_ptr<ControlFlowGraph> cfg);
  ~CPOptimization();

  virtual std::shared_ptr<InstructionSequence>
    transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb);
};

// Function to remove all occurrences of a value in all vectors in the map
void removeValueFromVecInMap(std::map<int, std::vector<int>>& map, int valueToRemove);

// Function to remove all pairs with a specific value from the map
void removePairsWithValue(std::map<int, int>& myMap, int valueToRemove);

int findValueInMap(const std::map<int, std::vector<int>>& myMap, int valueToFind);

class LRAOptimization : public ControlFlowGraphTransform {
private:
  LiveVregs m_live_vregs;
  std::shared_ptr<Function> m_function;
  int m_spilledStorage;

public:
  LRAOptimization(std::shared_ptr<ControlFlowGraph> cfg, std::shared_ptr<Function> func);
  ~LRAOptimization();

  virtual std::shared_ptr<InstructionSequence>
    transform_basic_block(std::shared_ptr<InstructionSequence> orig_bb);

  int get_spilledStorage() const {
    return m_spilledStorage;
  }

};

void removeValueFromDeque(std::deque<int>& deq, int valueToRemove);
bool isValueInVector(const std::vector<int>& vec, int valueToFind);
int stealMachineReg(std::map<int,int>& AssignMap, std::shared_ptr<InstructionSequence> result_iseq,
                           unsigned offset,std::map<int,int>& spilledMap, int& spilled_storage);

void restoreVreg(std::shared_ptr<InstructionSequence> result_iseq, int base_reg, int MR, HighLevelOpcode opcode, std::map<int,int>& spilledMap);

int assignMreg(std::shared_ptr<InstructionSequence> result_iseq, std::map<int,int>& spilledMap,
               std::map<int,int>& AssignMap, std::deque<int> &M_Queue, int& spilled_storage,
               int base_reg, std::shared_ptr<Function> m_function);
#endif // CFG_TRANSFORM_H


// PROBLEM:
//    A) TRANSFORM_BASIC_BLOCK NEEDS TO KNOW THE OFFSET WHERE IT CAN PLACE SPILLS
//    B) TRANSFORM_BASIC_BLOCK NEEDS TO CONVEY THE STORAGE NEEDED FOR SPILLS
//    C) TRANSFORM_BASIC_BLOCK NEEDS TO KNOW THE NUMBER REGISTERS USED FOR LOCAL VARIABLES

// SOLUTION:
//    A) NEW FIELD IN INSTRUCTIONSEQUENCE -> OFFSET FOR PLACING SPILLS
//    B) NEW FIELD IN INSTRUCTIONSEQUENCE -> STORAGE USED FOR SPILLS
//    C) NEW FIELD IN INSTRUCIONSEQUENCE  -> NUMBER OF REGISTERS USED FOR LOCAL VARIABLES

