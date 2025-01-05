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
#include "symtab.h"
#include "local_storage_allocation.h"

#include <iostream>

#include "ast.h"
#include "parse.tab.h"
#include "vreg_allocator.h"

LocalStorageAllocation::LocalStorageAllocation()
  : m_total_local_storage(0U)
  , m_next_vreg(VREG_FIRST_LOCAL) {
}

LocalStorageAllocation::~LocalStorageAllocation() {
}

void LocalStorageAllocation::allocate_storage(std::shared_ptr<Function> function) {
  // Any member function can use m_function to refer to the
  // Function object.
  m_function = function;
  //printf("ENTERING LOCAL STORAGE ALLOCATION\n");
  visit(function->get_funcdef_ast());
  //printf("EXITING LOCAL STORAGE ALLOCATION\n");
}

// NOTE: IT IS NOT THE LocalStorageAllocator's job to do the following:
//       1. Create Labels
//       2. Allocate storage for temporary variables.

void LocalStorageAllocation::visit_function_definition(Node *n) {
  //StorageAllocation for a function definition should:
  //1. Determine storage location (memory or vreg) for each parameter and each local variable in func
  //  a. VREG should be used when: param/var is either integral/pointer & address is never taken.
  //  b. Memory should be used when: param/var is either struct/array or param/var with address taken.

  //Need to be able to determine whether param/variable address ever taken
  //    Solution: During semantic analysis annotate the Symbol of the var/param whenever unary & operation used
  //              Requires: Extra field in Symbol - bool m_isTaken
  //              STATUS: DONE/IMPLEMENTED

  // Algorithm:
  //    1. For every parameter.
  //      a. Based on the symboltype and the isTaken field, determine whether to allocate VREG or Memory
  //      b. Record decision in Symbol field Operand
  //      c. Update m_total_local_storage (add entry storage size)
  //      d. if VREG chosen, increment m_next_vreg
  //    2. Visit statementlist

  //  1. When allocating storage for memory reference we:
  //      - Allocate vreg (!!!!!!)
  //      - Create Operand of VREG_mem type with
  //          - base reg = vreg
  //          - imm val = offset (current m_total_local_storage)
  //      - update m_total_local_storage

  //IMPORTANT DECISION:
  // - We allocate a vreg for memory references
  // - We could choose NOT to do this, and do it dynamically instead
  //    - (how it is done in examples)
  // - Should not be problematic to do it in this fashion.
  // - Alternative:
  //  - Do not allocate vreg
  //  - Use garbage value in created Operand for base reg
  //  - Allocate temp var whenever param is referenced.

  //Create V_reg_allocator
  auto VregAlloc = m_function->get_vregAlloc();
  VregAlloc->reset(m_next_vreg); //Initialize to 10

  //Get paramlist
  auto paramlist = n->get_kid(2);

  //Get symboltable
  SymbolTable* symtab = n->get_symbol_ptr()->get_symtab();

  //PART 1:
  for(auto i = 0U; i < paramlist->get_num_kids();i++) {
    auto param = paramlist->get_kid(i);
    auto param_name = param->get_string();
    auto param_sym = symtab->lookup_local(param_name);
    auto param_type = param->get_type();
    auto storage_size = param_type->get_storage_size();
    //If array or struct or if address taken:
    //Allocate memory:
    //Use m_total_local_storage
    //Update m_total_local_storage using get_storage_size
    if(param_type->is_array()||param_sym->get_isTaken()||param_type->is_struct()) {
      Operand operand(Operand::VREG_MEM, -1); //dummy value for ival -> store mem_loc in set_mem_loc
      param_sym->set_Operand(operand);
      param_sym->set_mem_loc(m_total_local_storage);
      param->set_symbol(param_sym);

      //printf("/* ALLOCATED %d BYTES OF STORAGE AT OFFSET %d FOR VARIABLE %s */ \n",
                             //storage_size, m_total_local_storage, param_name.c_str());

      //Update total_local_storage
      //if ((storage_size) % 8 != 0) storage_size += (8 - (storage_size % 8));
      m_total_local_storage += storage_size; // Calculate New Offset
    }
    //else (if integral/pointer and address not taken)
    else{
      //Allocate VREG
      //use Vreg_allocator?
      auto num = VregAlloc->alloc_param();
      Operand operand(Operand::VREG, num);
      param_sym->set_Operand(operand);
      //printf("ALLOCATED REG AT %d FOR PARAM VAR %s\n", num, param_name.c_str());

    }
  }

  //Finished adding all params
  VregAlloc->end_params();

  //PART 2:
  //Visit the statementlist
  if(n->get_num_kids() >= 4) {
    visit(n->get_kid(3));
  }

  //Propagate the total amount of local storage needed to function object
  //Used in next stage (codegen)

  m_function->set_total_storage(m_total_local_storage);
}

void LocalStorageAllocation::visit_statement_list(Node *n) {
  //Storage Allocation for a statement List should

  //2. Visit all children, but do it in a certain manner:
  //  I. First visit all children of type Variable declaration
  //  II. Then visit all other children types.

  //This ensures that VREGS  are allocated in a certain order
  //Such that in every scope / statement list all local variables are assigned a VREG
  //Before any local variables in a nested statement list are assigned a VREG.

  auto num_kids = n->get_num_kids();

  //FIRST VISIT ALL VARIABLE DECLARATION CHILDREN
  for(auto i = 0U; i < num_kids;i++) {
    if(n->get_kid(i)->get_tag() == AST_VARIABLE_DECLARATION) visit(n->get_kid(i));
  }
  //THEN VISIT ALL OTHER CHILDREN
  for(auto i = 0U; i < num_kids;i++) {
    if(n->get_kid(i)->get_tag() != AST_VARIABLE_DECLARATION) visit(n->get_kid(i));
  }
}

void LocalStorageAllocation::visit_variable_declaration(Node *n) {
  //a. When variable declaration found:
  //   - Allocate memory for local variables (VREG or memory)
  auto VregAllocator = m_function->get_vregAlloc();

  auto decl_list = n->get_kid(2);

  //For every declarator, we need to allocate memory (VREG or memory)
  for(auto i = 0U; i < decl_list->get_num_kids();i++) {
    auto var = decl_list->get_kid(i);
    auto var_sym = var->get_symbol_ptr();
    auto var_type = var->get_type();
    auto storage_size = var_type->get_storage_size();

    if(var_type->is_array()||var_sym->get_isTaken()||var_type->is_struct()) {
      auto operand = Operand(Operand::VREG_MEM, -1); //Dummy ival1
      var_sym->set_Operand(operand);
      var_sym->set_mem_loc(m_total_local_storage);
      //Update total_local_storage
      //printf("/*ALLOCATED %d BYTES AT %d FOR LOCAL VAR %s */\n",storage_size, var_sym->get_mem_loc(), var->get_string().c_str());
      //if ((storage_size) % 8 != 0) storage_size += (8 - (storage_size % 8));
      m_total_local_storage += storage_size; // Calculate New Offset
    }
    //else (if integral/pointer and address not taken)
    else{
      //Allocate VREG
      auto num = VregAllocator->alloc_local();
      Operand operand(Operand::VREG, num);
      var_sym->set_Operand(operand);
      //printf("/*ALLOCATED REG %d FOR LOCAL VAR %s */\n",num, var->get_string().c_str());
    }
  }
}
