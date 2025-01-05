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

#ifndef NODE_BASE_H
#define NODE_BASE_H

#include <memory>
#include "type.h"
#include "symtab.h"
#include "literal_value.h"
#include "has_operand.h"
#include <cassert>

//! The Node class will inherit from this type, so you can use it
//! to define any attributes and methods that Node objects should have
//! (constant value, results of semantic analysis, code generation info,
//! etc.)
//!
//! Because NodeBase inherits from HasOperand, each Node automatically
//! stores an Operand. This is useful for code generation: when
//! generating code to evaluate an expression, HighLevelCodegen
//! can set the Node's Operation to indicate the location where the
//! result of the evaluation is stored.
class NodeBase : public HasOperand {
private:
  std::shared_ptr<Type> m_type_ptr; //pointer to type
  Symbol* m_symbol_ptr; //pointer to symbol
  bool m_isLval; //bool for deciding if expression node yields lVal.
  LiteralValue m_litVal;
  std::string m_string;
  Operand m_operand;
  unsigned m_memory_loc;

  // copy constructor and assignment operator not supported
  NodeBase(const NodeBase &);
  NodeBase &operator=(const NodeBase &);

public:
  NodeBase();
  virtual ~NodeBase();

  void set_string(std::string string) {
    m_string = string;
  }
  std::string get_string() {
    return m_string;
  }

  void set_type(const std::shared_ptr<Type> &type) {
    remove_symbol();
    remove_type();
    assert(!has_symbol());
    assert(!m_type_ptr);
    m_type_ptr = type;
  }

  void remove_type() {
    m_type_ptr = nullptr;
  }

  void remove_symbol() {
    m_symbol_ptr = nullptr;
  }

  std::shared_ptr<Type> get_type() const {
    // this shouldn't be called unless there is actually a type
    // associated with this node
    if (has_symbol())
      return m_symbol_ptr->get_type();
    else {
      assert(m_type_ptr); // make sure a Type object actually exists
      return m_type_ptr;
    }
  }

  void set_symbol(Symbol *symbol) {
    remove_symbol();
    remove_type();
    assert(!has_symbol());
    assert(this->m_type_ptr == nullptr);
    this->m_symbol_ptr = symbol;
  }
  bool has_symbol() const {
    return this->m_symbol_ptr != nullptr;
  }
  Symbol* get_symbol_ptr() const {
    assert(this->m_symbol_ptr != nullptr);
    return this->m_symbol_ptr;
  }
  void set_litVal(const LiteralValue &litVal) {
    this->m_litVal = litVal;
  }
  void set_isLval(bool Lval) {
    this->m_isLval = Lval;
  }
  bool get_isLval() {
    return m_isLval;
  }
  LiteralValue get_litval() {
    return m_litVal;
  }

  void set_Node_Operand(Operand op) {
    m_operand = op;
  }
  Operand get_Node_Operand() {
    return m_operand;
  }

};

#endif // NODE_BASE_H
