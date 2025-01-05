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
#include <algorithm>
#include <utility>
#include <map>
#include "grammar_symbols.h"
#include "parse.tab.h"
#include "node.h"
#include "ast.h"
#include "exceptions.h"
#include "semantic_analysis.h"

SemanticAnalysis::SemanticAnalysis(const Options &options)
  : m_options(options)
  , m_global_symtab(new SymbolTable(nullptr, "global")) {
  m_cur_symtab = m_global_symtab;
  m_all_symtabs.push_back(m_global_symtab);
}

SemanticAnalysis::~SemanticAnalysis() {
  // The semantic analyzer owns the SymbolTables and their Symbols,
  // so delete them. Note that the AST has pointers to Symbol objects,
  // so the SemanticAnalysis object should live at least as long
  // as the AST.
  for (auto i = m_all_symtabs.begin(); i != m_all_symtabs.end(); ++i)
    delete *i;
}

//Check that struct type exists
//Annotate node with type
void SemanticAnalysis::visit_struct_type(Node *n) {
  auto name = n->get_kid(0)->get_str();
  auto sym = m_cur_symtab->lookup_recursive("struct "+name);
  if(sym == nullptr) {
    SemanticError::raise(n->get_loc(),"SemanticError: Struct type not defined");
  }
  n->set_type(sym->get_type());
}

void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

void SemanticAnalysis::visit_variable_declaration(Node *n) {
  // Should visit base type first
  visit(n->get_kid(1));
  std::shared_ptr<Type> base_type = n->get_kid(1)->get_type();

  //Iterate through the declarators. Add Variables to symbol table.

  Node *decl_list = n->get_kid(2);
  for(auto i = decl_list->cbegin(); i != decl_list->cend(); ++i) {
    Node *declarator = *i;
    //Need to:
    //Annotate declarator node with type (needed for creating symbol later)
    declarator->set_type(base_type);
    //Visit the declarator
    visit(declarator);
    auto leaf_node = declarator;
    while(leaf_node->get_kid(0)->get_tag() != TOK_IDENT) {
      if(leaf_node->get_num_kids() == 0) {
        SemanticError::raise(n->get_loc(), "SemanticError: Illegal Variable Declaration");
      }
      leaf_node = leaf_node->get_kid(0);
    }
    auto type = leaf_node->get_type();
    auto symbol = m_cur_symtab->add_entry(n->get_loc(), SymbolKind::VARIABLE,declarator->get_string(), type);
    //remove the type, annotate top declarator of each variable with symbol
    declarator->set_symbol(symbol);
  }
}

void SemanticAnalysis::visit_basic_type(Node *n) {
  //For keywords
  bool basetypeFound = false;
  bool isSigned = false;
  bool isUnsigned = false;
  BasicTypeKind btk;
  //For Qualifiers
  bool isConst = false;
  bool isVolatile = false;
  //Check basetype keywords & qualifiers
  for(unsigned i = 0; i < n->get_num_kids(); i++) {
    auto child_tag = n->get_kid(i)->get_tag();
    switch (child_tag) {
      case(TOK_VOID): {
        if (basetypeFound == false) {
          basetypeFound = true;
          btk = BasicTypeKind::VOID;
        }
        else {
          SemanticError::raise(n->get_loc(), "Invalid typing, multiple basetypes");
        }
        if(isSigned || isUnsigned || isConst || isVolatile) {
          SemanticError::raise(n->get_loc(), "Invalid typing VOID cannot be signed/qualified");
        }
        break;
      }
      case(TOK_INT): {
        if (basetypeFound == false) {
          basetypeFound = true;
          btk = BasicTypeKind::INT;
        }
        else {
          //When we see an int, we might already have seen short/long.
          //We might also already have seen signed / unsigned.
          //no error in these cases.
          //if we already seen int, void or char, we have error.
          if ( (btk == BasicTypeKind::VOID) || (btk == BasicTypeKind::CHAR) || (btk == BasicTypeKind::INT)) {
          SemanticError::raise(n->get_loc(), "Invalid typing, multiple basetypes");
          }
        }
        break;
      }
      case(TOK_CHAR): {
        if (basetypeFound == false) {
          basetypeFound = true;
          btk = BasicTypeKind::CHAR;
        }
        else {
          SemanticError::raise(n->get_loc(), "Invalid typing, multiple basetypes");
        }
        break;
      }
      case(TOK_LONG): {
        if (basetypeFound == false) {
          basetypeFound = true;
          btk = BasicTypeKind::LONG;
        }
        else {
          // LONG INT and INT LONG allowed (no error) -> We simplify to just LONG in this case.
          if(btk == BasicTypeKind::INT) {
            btk = BasicTypeKind::LONG;
          }
          else {
          SemanticError::raise(n->get_loc(), "Invalid typing, multiple basetypes");
          }
        }
        break;
      }
      case(TOK_SHORT): {
        if (basetypeFound == false) {
          basetypeFound = true;
          btk = BasicTypeKind::SHORT;
        }
        else {
          // SHORT INT and INT SHORT allowed (no error) -> We simplify to just SHORT in this case.
          if(btk == BasicTypeKind::INT) {
            btk = BasicTypeKind::SHORT;
          }
          else {
            SemanticError::raise(n->get_loc(), "Invalid typing, unsigned/signed error");
          }
        }
        break;
      }
      case(TOK_SIGNED): {
        if(isUnsigned == true || isSigned == true) {
          SemanticError::raise(n->get_loc(), "Invalid typing, unsigned/signed error");
        }
        isSigned = true;
        break;
      }
      case(TOK_UNSIGNED): {
        if(isSigned == true || isUnsigned == true) {
          SemanticError::raise(n->get_loc(), "Invalid typing, unsigned/signed error");
        }
        isUnsigned = true;
        break;
      }
      case(TOK_CONST): {
        if(isConst == false) {
          isConst = true;
        }
        else {
          SemanticError::raise(n->get_loc(), "Invalid typing, Qualifier Error");
        }
        break;
      }
      case(TOK_VOLATILE):{
        if(isVolatile == false) {
          isVolatile = true;
        }
        else {
          SemanticError::raise(n->get_loc(), "Invalid typing, Qualifier Error");
        }
        break;
      }
      default: {
        break;
      }
    }
  }

  //Only seen "signed" or "unsigned", no base type seen
  //INT should then be the base type (unsigned same as unsigned int)
  if(basetypeFound == false) {
    if(isUnsigned || isSigned) {
      btk = BasicTypeKind::INT;
    }
  }

  //if neither unsigned or signed specified, we should assume signed
  if(basetypeFound == true) {
    if((!isUnsigned) && (!isSigned)) {
      isSigned = true;
    }
  }

  //Create BasicType object (wrapped in shared smart pointer) to represent basic type
  std::shared_ptr<Type> basicTypePtr(new BasicType(btk, isSigned));
  //If qualifier specified, Wrap BasicType in QualifiedType.
  //If two qualifier specified, Wrap first QualifiedType in second QualifiedType
  if(isVolatile) {
    std::shared_ptr<Type> qualifiedTypePtrVOLATILE(new QualifiedType(basicTypePtr, TypeQualifier::VOLATILE));
    if(isConst) {
      std::shared_ptr<Type> qualifiedTypePtrCONST(new QualifiedType(qualifiedTypePtrVOLATILE, TypeQualifier::CONST));
      n->set_type(qualifiedTypePtrCONST);
    }
    else {
      n->set_type(qualifiedTypePtrVOLATILE);
    }
  }
  else if (isConst){ //If no qualifier we can pass the basicTypePtr directly.
    std::shared_ptr<Type> qualifiedTypePtrCONST(new QualifiedType(basicTypePtr, TypeQualifier::CONST));
    n->set_type(qualifiedTypePtrCONST);
  }
  else {
    n->set_type(basicTypePtr);
  }
}

//visiting named declarator should:
//1. Create symbol table entry in current symbol table
//2. Set pointer to symbol table entry in node
void SemanticAnalysis::visit_named_declarator(Node *n) {
  Node* ident = n->get_kid(0);
  auto identifier = ident->get_str();
  n->set_string(identifier);
}

void SemanticAnalysis::visit_pointer_declarator(Node *n) {
  //For the pointer declarator we need to include that this is a pointer.
  //create new PointerType from old basetype
  std::shared_ptr<Type> pointerTypeptr(new PointerType(n->get_type()));
  //Visit child (named_declarator node)
  Node *declarator = n->get_kid(0);
  //pass base type along to child (use for symbol table creation).
  declarator->set_type(pointerTypeptr);
  //Visit declarator
  visit(declarator);
  n->set_string(declarator->get_string());
}

void SemanticAnalysis::visit_array_declarator(Node *n) {
  //same deal as visiting pointer declarator
  //Get array size from kid(1) by using LiteralValue class
  auto litVal = LiteralValue::from_int_literal(n->get_kid(1)->get_str(), n->get_kid(0)->get_loc());
  auto size = litVal.get_int_value();
  //create new ArrayType from old basetype
  std::shared_ptr<Type> ArrayTypeptr(new ArrayType(n->get_type(),size));
  //Visit child (named declarator node)
  Node *declarator = n->get_kid(0);
  //pass base type along to child (use for symbol table creation).
  declarator->set_type(ArrayTypeptr);
  //Visit declarator
  visit(declarator);
  n->set_string(declarator->get_string());
}

//This should:
// Check if function already in global scope
/*  NO:
 *    1. Create Functiontype representing functions type
 *    2. Enter new symboltable scope
 *    3. Visit parameters (create symbol table entries).
 *    4. Add parameters as members to FunctionType.
 *    5. Annotate Node with return type
 *    6. Visit statementlist (add symbols to function symbol table)
 *    7. Leave the scope (Function symbol table)
 *    8. Add Function to global scope
 *    9. Annotate Node with ptr to function
 *  YES:
 *    0. Create Functiontype representing functions type
 *    1. Compare current function def/dec with the one in symboltable
 *        -> Check return type, number of parameters, type of parameters.
 *    2. Enter function's param/body symboltable
 *    3. Overwrite parameter names
 *    4. Visit statementList
 *    5. Leave the scope (Function Symbol table)
 *    6. Annotate Node with ptr to function
 *    7. Annotate Node with return type of function
*/
void SemanticAnalysis::visit_function_definition(Node *n) {
  //printf("VISIT FUNCTION DEFINITION\n");
  auto BT = n->get_kid(0);
  visit(BT);
  auto ident = n->get_kid(1);
  auto param_list = n->get_kid(2);
  auto stmt_list = n->get_kid(3);
  auto name = ident->get_str();
  auto scope_name = "function "+name;
  auto sym = m_cur_symtab->lookup_recursive(name);

  //Function definition only allowed if in global symbol table
  if(this->m_cur_symtab != get_global_symtab()) {
    SemanticError::raise(n->get_loc(), "Function definition not allowed inside inner scope");
  }

  n->set_string(name);

  //FUNC NOT ALREADY DECLARED/DEFINED
  if(sym == nullptr) {
    //Create FunctionType Representing Function Type
    std::shared_ptr<Type> FunctionTypePtr(new FunctionType(BT->get_type()));
    //Enter new scope (new symbol table)
    enter_scope(scope_name);
    //add Parameters to new symbol table scope
    //Visit parameters (add to symbol table, annotate AST)
    param_list->set_type(FunctionTypePtr);
    visit(param_list);
    //Visit statementList -- add var defs to symbol table
    //Base type propagate to statementList -> needed to check return type
    stmt_list->set_type(param_list->get_type()->get_base_type());
    stmt_list->set_string("function");
    visit(stmt_list);
    //Leave the scope
    //Add function to global scope
    n->set_symbol(m_global_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION, name, param_list->get_type()));
    n->get_symbol_ptr()->set_symtab(m_cur_symtab);
    leave_scope();

  }

  //FUNC ALREADY DEFINED/DECLARED
  else {
    if(sym->get_kind() == SymbolKind::FUNCTION) {
      if(not sym->get_type()->get_base_type()->is_same(BT->get_type().get())) {
        SemanticError::raise(n->get_loc(), "SemanticError: Function return type match issue");
      }
      if(param_list->get_num_kids() != sym->get_type()->get_num_members()) {
        SemanticError::raise(n->get_loc(), "SemanticError: Function parameter num issue");
      }
      //For member x in sym, check if param x in param_list has same type
      for(unsigned i = 0; i < param_list->get_num_kids(); i++) {
        auto oldparam = sym->get_type()->get_member(i);
        auto oldparam_type = oldparam.get_type();
        auto current_param = param_list->get_kid(i);
        visit(current_param->get_kid(0));
        visit(current_param->get_kid(1));
        auto current_param_type = current_param->get_kid(0)->get_type();
        if(not oldparam_type->is_same(current_param_type.get())) {
          SemanticError::raise(n->get_loc(), "SemanticError: Function parameter num issue");
        }
      }
      //Get original Function symbol table
      SymbolTable *fn_symtab = get_symtab(scope_name);
      if(fn_symtab == nullptr) {
        SemanticError::raise(n->get_loc(), "SemanticError: No associated Symboltable found to defined/declared func");
      }
      //Check that Function not already defined (not allowed multiple definitions)
      //If number of entries in original symtab > number of parameters

      //Enter original Function Symbol table
      auto prior_symtab = m_cur_symtab;
      m_cur_symtab = fn_symtab;
      //Overwrite parameter names
      overwriteParameters(param_list,m_cur_symtab);
      //Visit statement list
      stmt_list->set_type(sym->get_type()->get_base_type());
      stmt_list->set_string("function");
      visit(stmt_list);
      //Leave scope
      m_cur_symtab = prior_symtab;
      //annotate node with symbol ptr
      n->set_symbol(sym);
    }
    else {
      SemanticError::raise(n->get_loc(), "SemanticError: Name already in use (function definition)");
    }
  }
}

//Same deal as for function_definition with a few changes:
//1. This should not visit the body (as there is no statementlist)
//2. This should not rename any parameters if function already declared/defined
//3. No reason to enter old scope - (neither overwriting param names or visiting stmtlist)
//                                - We can also compare the two FunctionTypes without entering
void SemanticAnalysis::visit_function_declaration(Node *n) {
  //printf("VISIT FUNCTION DECLARATION\n");
  auto BT = n->get_kid(0);
  visit(BT);
  auto ident = n->get_kid(1);
  auto param_list = n->get_kid(2);
  auto name = ident->get_str();
  std::string scope_name = "function "+name;
  auto sym = m_cur_symtab->lookup_local(name);

  //Function declaration only allowed if in global symbol table (no lambdas)
  if(this->m_cur_symtab != this->get_global_symtab()) {
    SemanticError::raise(n->get_loc(), "Function declaration not allowed inside inner scope");
  }

  //FUNC NOT ALREADY DECLARED/DEFINED
  if(sym == nullptr) {
    //Create FunctionType Representing Function Type
    std::shared_ptr<Type> FunctionTypePtr(new FunctionType(BT->get_type()));
    //Enter new scope (new symbol table)
    enter_scope(scope_name);
    //add Parameters to new symbol table scope
    //Visit parameters (add to symbol table, annotate AST)
    param_list->set_type(FunctionTypePtr);
    visit(param_list);
    //Add function to global scope
    n->set_symbol(m_global_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION, name, param_list->get_type()));
    n->get_symbol_ptr()->set_symtab(m_cur_symtab);
    //Leave the scope
    leave_scope();
  }

  //FUNC ALREADY DEFINED/DECLARED
  else {
    if(sym->get_kind() == SymbolKind::FUNCTION) {
      if(not sym->get_type()->get_base_type()->is_same(BT->get_type().get())) {
        //BASETYPE NOT THE SAME
        SemanticError::raise(n->get_loc(), "SemanticError: Function return type match issue");
      }
      if(param_list->get_num_kids() != sym->get_type()->get_num_members()) {
        //NUMBER OF PARAMETERS NOT THE SAME
        SemanticError::raise(n->get_loc(), "SemanticError: Function parameter num issue");
      }
      //For member x in sym, check if param x in param_list has same type
      for(unsigned i = 0; i < param_list->get_num_kids();i++) {
        if(not sym->get_type()->get_member(i).get_type()->is_same(param_list->get_kid(i)->get_kid(0)->get_type().get())) {
          //TYPE OF PARAMETERS NOT THE SAME
          SemanticError::raise(n->get_loc(), "SemanticError: Function parameter num issue");
        }
      }
      //annotate node with symbol ptr
      n->set_symbol(sym);
    }
    else {
      SemanticError::raise(n->get_loc(), "SemanticError: Name already in use (function declaration)");
    }
  }
}

//For Function parameter list we want to:
//1. Visit all children (parameters)
//    -- Visit should add parameters to function symbol table
//2. Add each parameter as Member in FunctionType
void SemanticAnalysis::visit_function_parameter_list(Node *n) {
  //printf("VISIT FUNCTION PARAMETER LIST\n");
  for(unsigned i = 0; i < n->get_num_kids(); i++) {
    //(1) Visit function parameters
    auto func_param = n->get_kid(i);
    visit(func_param);
    //(2) Add parameters as members to functiontype
    //    Access type in function_parameter node for type
    n->get_type()->add_member(Member(func_param->get_string(),func_param->get_type()));
  }
}

//For a function parameter we want to
//  Annotate named declarator node with type from base type
//  Visit named declarator (child 1) (will add symbol to symboltable)
void SemanticAnalysis::visit_function_parameter(Node *n) {
  //printf("VISIT FUNCTION PARAMETER\n");
  auto base = n->get_kid(0);
  auto named_dec= n->get_kid(1);
  //Visit children (base type, named declarator)
  visit(base); //gets type of param
  std::shared_ptr<Type> base_type = n->get_kid(0)->get_type();
  named_dec->set_type(base_type);
  visit(named_dec); //Modifies base_type, propagates identifier

  auto leaf_node = named_dec;
  while(leaf_node->get_kid(0)->get_tag() != TOK_IDENT) {
    if(leaf_node->get_num_kids() == 0) {
      SemanticError::raise(n->get_loc(), "SemanticError: Function parameter trouble");
    }
    leaf_node = leaf_node->get_kid(0);
  }
  auto type = leaf_node->get_type();
  //Add variable to local symbol table

  if(type->is_array()) {
    base_type = type->get_base_type();
    std::shared_ptr<Type> pointerTypeptr(new PointerType(base_type));
    type = pointerTypeptr;
  }
  Symbol* sym;
  if(type->is_struct()) {
    sym = m_cur_symtab->add_entry(n->get_loc(), SymbolKind::TYPE,named_dec->get_string(), type);
  }
  else if(type->is_function()) {
    sym = m_cur_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION,named_dec->get_string(), type);
  }
  else {
    sym = m_cur_symtab->add_entry(n->get_loc(), SymbolKind::VARIABLE,named_dec->get_string(), type);
  }
  n->set_symbol(sym);
  n->set_string(named_dec->get_string());
}

//In the statement list we simply want to visit all children
//Should not annotate with anything (type, symbol)
//Should enter a new scope (if not part of a function definition, already entered).
void SemanticAnalysis::visit_statement_list(Node *n) {
  //printf("VISIT STATEMENT LIST\n");
  if(not(n->get_string() == "function")) {
    auto linenum = std::to_string(n->get_loc().get_line());
    enter_scope("block " + linenum);
    n->set_string(linenum);
  }
  //Statement list should
  for(auto i = n->cbegin(); i != n->cend(); ++i) {
    auto *stmt = *i;
    if(stmt->get_tag() == AST_RETURN_EXPRESSION_STATEMENT) {
      //Propagate return type
      stmt->set_type(n->get_type());
    }
    else if(stmt->get_tag() == AST_RETURN_STATEMENT){
      if (not n->get_type()->is_void()) {
        SemanticError::raise(n->get_loc(), "SemanticError: Wrong return statement type");
      }
    }
    visit(stmt);
  }
  if(not(n->get_string() == "function")) {
    leave_scope();
  }
  //printf("EXIT STATEMENT LIST\n");

}

//Need to check that type == function return type
//Therefore propagating the function return type down here is important.
void SemanticAnalysis::visit_return_expression_statement(Node *n) {
  visit(n->get_kid(0));
  auto returntype = n->get_type();
  auto type = n->get_kid(0)->get_type();
  if(not returntype->is_same(type.get())) {
    if(returntype->is_integral() && type->is_integral()) {
      if(returntype->get_basic_type_kind() > type->get_basic_type_kind()) {
        auto basic_type = returntype->get_basic_type_kind();
        switch (basic_type) {
          case BasicTypeKind::SHORT: {
            n->set_kid(0, promote_to_short(n->get_kid(0)));
            break;
          }
          case BasicTypeKind::INT: {
            n->set_kid(0, promote_to_int(n->get_kid(0)));
            break;
          }
          case BasicTypeKind::LONG: {
            n->set_kid(0, promote_to_long(n->get_kid(0)));
            break;
          }
          default: {
            break;
          }
        }
      }
    }
    else{
      SemanticError::raise(n->get_loc(), "SemanticError: Wrong return statement type");
    }
  }
}

//Create StructType -> put into current symboltable
//Enter struct symboltable
//visit Field definition list (child(1))
//For each entry in new symboltable -> add member to Structype.
//Leave struct symboltable
//Annotate node with pointer to symbol of struct
void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  std::string name = n->get_kid(0)->get_str();
  Location loc = n->get_loc();
  //Create new struct_type:
  std::shared_ptr<Type> struct_type(new StructType(name));
  //Add struct symbol to current symbol table AND Store symbol pointer in node
  n->set_symbol(m_cur_symtab->add_entry(loc,SymbolKind::TYPE,"struct " + name, struct_type));

  //Enter struct symbol table
  //Looking at public test cases -> symbol table name = struct /name/
  enter_scope("struct " + name);

  //Visit each child of Field Definition list
  auto Field_def_list = n->get_kid(1);
  for(unsigned i = 0; i < Field_def_list->get_num_kids(); i++) {
    //Should add all variable declarations to struct symboltable
    visit(Field_def_list->get_kid(i));
  }
  //Add each field as member in structType
  for(unsigned i = 0 ; i < m_cur_symtab->get_num_entries();i++) {
    auto field = m_cur_symtab->get_entry(i);
    auto field_name = field->get_name();
    auto field_type = field->get_type();
    struct_type->add_member(Member(field_name, field_type));
  }
  //Leave scope
  leave_scope();
}

void SemanticAnalysis::visit_binary_expression(Node *n) {
  //printf("BINARY EXPRESSION\n");
  // Binary expressions are:
  // 1. Arithmetic (+,-,*,/,%)
  // 2. Assignments
  // 3. Relational Operators (<, <=, >, >=, ==, !=)
  // 4. Logical (&&, ||)

  // Binary expressions are:
  // Executed on two operators, which must have the types:
  // Numeric, Pointer, or Struct.
  // The following mixes are allowed:
  // 1. N  N
  // 2. N +- P  //  P +- N
  // 3. S = S

  // Arithmetic on two pointers is never allowed.
  // Arithmetic on pointer and integer is pointer arithmetic -> allowed.
  //    Integer Operand promoted to INT or unsigned INT if less precise.

  // IMPORTANT: Promotions and implicit conversions must be handled
  // 1. If either operand has a type less precise than INT or unsigned INT
  //    it is promoted to INT or unsigned INT.
  // 2. If one operand is less precise than the other, it is promoted
  // 3. If operands differ in signedness, signed operand is converted to unsigned.

  // Assignments:
  // Not allowed if left hand operand is qualified as const
  // Only allowed if left hand side op is lvalue
  // Right hand type implicitly converted to left hand lvalue type.
  // If both sides are pointers, then assignment legal only if:
  //  1. Unqualified base types of each pointer matching
  //  2. Base type of left hand side NO Less qualified than base type of right side.
  // Never allowed if involving both pointer and non-pointer operands.
  // For STRUCTS: only allowed if both operands are the same struct type.

  // Return type:
  // 1. INT for relational and logical operators
  // 2. For others, the type of the operands (which should be the same).

  // Visit the two operator nodes used in expression
  visit(n->get_kid(1));
  //printf("VISITED KID 1\n");
  visit(n->get_kid(2));
  //printf("VISITED KID 2\n");

  // We need: Switch statement based on tag of first child
  auto kind = n->get_kid(0)->get_tag();
  auto l_op = n->get_kid(1);
  auto r_op = n->get_kid(2);
  auto l_op_t = l_op->get_type();
  auto r_op_t = r_op->get_type();

  switch(kind) {
    //ARITHMETIC
    case TOK_MINUS: //MINUS AND PLUS THE SAME, POINTER ARITHMETIC ALLOWED
    case TOK_PLUS: {
      //When dealing with an array-type we restructure it into the equivalent pointer
      if(l_op_t->is_array()) {
        std::shared_ptr<Type> pointerTypeptr(new PointerType(l_op_t->get_base_type()));
        l_op_t = pointerTypeptr;
      }
      if(r_op_t->is_array()) {
        std::shared_ptr<Type> pointerTypeptr(new PointerType(r_op_t->get_base_type()));
        r_op_t = pointerTypeptr;
      }
      //Both operators are pointers -> error
      if(l_op_t->is_pointer() && r_op_t->is_pointer()) {
        SemanticError::raise(n->get_loc(), "Semantic Error: Binary expression arithmetic with two pointers");
      }
      //Atleast one operator is struct -> error
      if(l_op_t->is_struct() || r_op_t->is_struct()) {
        SemanticError::raise(n->get_loc(), "Semantic Error: Binary expression arithmetic with struct");
      }
      //One operator is pointer && other operator is integer
      if(l_op_t->is_pointer() && r_op_t->is_integral()) {
        //Make sure right op is promoted to at least INT
        if(r_op_t->get_basic_type_kind() <  BasicTypeKind::INT) {
          n->set_kid(2, promote_to_int(r_op));
        }
        //Annotate result node with same type as pointer
        n->set_type(l_op_t);
        //LVALUE -> could assign to pointer arithmetic expr
        n->set_isLval(true);
      }
      else if(l_op_t -> is_integral() && r_op_t->is_pointer()) {
        //Make sure left op is promoted to at least INT
        if(l_op_t->get_basic_type_kind() <  BasicTypeKind::INT) {
          n->set_kid(1, promote_to_int(l_op));
        }
        //Annotate result node with same type as pointer
        n->set_type(r_op_t);
        //LVALUE -> could assign to pointer arithmetic expr
        n->set_isLval(true);
      }
      //Both operators are integers
      else if(l_op_t -> is_integral() && r_op_t->is_integral()) {
        //printf("BOTH ARE INTEGRAL\n");
        //Call helper function
        //Handles promotions, conversions.
        bin_exp_N_N(n);
        //lastly the result node is annotated with the type of the operators (the same)
        n->set_type(r_op_t);
        n->set_isLval(false);
        //printf("CHECK\n");
      }
      else {
        SemanticError::raise(n->get_loc(),"SemanticError: Invalid Binary Expression (typing)");
      }
      break;
    }
    case TOK_MOD:       //MOD, DIVIDE, MULTIPLY THE SAME
    case TOK_DIVIDE:    //ONLY FOR BOTH OP = NUMERIC (integral)
    case TOK_ASTERISK: {
      if(l_op_t -> is_integral() && r_op_t->is_integral()) {
        //Call helper function
        //Handles promotions, conversions.
        bin_exp_N_N(n);
        //lastly the result node is annotated with the type of the operators (the same)
        n->set_type(r_op->get_type());
        n->set_isLval(false);
      }
      else {
        SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr arithmetic");
      }
      break;
    }

    //ASSIGNMENTS
    case TOK_ASSIGN: {
      //Check that left op is lVal
      //Check that left op is NOT const
      //Check that left and right side is:
      // A) both integer (right op is converted to left op type)
      // B) both pointers
      //    - Unqualified base types identical
      //    - left op base type has at least the same qualifiers as right op
      // C) both same struct type

      if(r_op_t->is_array()) {
        std::shared_ptr<Type> pointerTypeptr(new PointerType(r_op_t->get_base_type()));
        r_op_t = pointerTypeptr;
      }

      //LEFT OP MUST NOT BE CONST
      if(l_op_t->is_const()) {
        SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) to CONST");
      }
      //LEFT OP MUST BE LVAL
      if(l_op->get_isLval() == false){
        SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) to non-Lval");
      }
      //NO MIX OF NON-POINTER AND POINTER OPERANDS
      if((l_op_t->is_pointer()) && (not r_op_t->is_pointer())) {
        SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) - pointer and non-pointer");
      }
      if((not l_op_t->is_pointer()) && (r_op_t->is_pointer())) {
        SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) - pointer and non-pointer");
      }

      //IF BOTH ARE INTEGRAL TYPE
      if(l_op_t->is_integral() && r_op_t->is_integral()) {
        //Implicitly convert r_op type to l_op type
        //Helper function which converts child(2) type (r_op) into child(1) type (l_op)
        if(not r_op_t->is_same(l_op_t.get())) {
          n->set_kid(2, convert_to_left_type(n));
        }
        //Annotate result node with l_op_type
        n->set_type(l_op_t);
        n->set_isLval(false);
      }
      //IF BOTH ARE POINTER TYPE
      //(1) Pointers must have identical unqualified base type
      //(2) Left pointer must be at least as qualified as right pointer
      //(3) Annotate node with result type
      //SHOULD RIGHT OP BE PROMOTED TO LEFT OP IF LEFT OP MORE QUALIFIED?
      else if(l_op_t->is_pointer() && r_op_t->is_pointer()) {
        auto l_bt = l_op_t->get_base_type();
        auto r_bt = r_op_t->get_base_type();
        //CHECK (1)
        if( not l_bt->get_unqualified_type()->is_same(l_bt->get_unqualified_type())) {
          SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) - type of pointers not matching");
        }
        //CHECK (2)
        if(r_bt->is_const() && (not l_bt->is_const())) {
          SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) - right pointer more qualified");
        }
        if(r_bt->is_volatile() && (not l_bt->is_volatile())) {
          SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) - right pointer more qualified");
        }
        //DO (3)
        n->set_type(l_op_t);
        n->set_isLval(false);
      }

      //IF BOTH ARE STRUCT TYPE
      else if(l_op_t->is_struct() && r_op_t->is_struct()) {
        //Check that struct type is the same
        //Access SymbolTable reference, extract type of both, compare
        if(l_op->get_symbol_ptr()->get_type()->is_same(r_op->get_symbol_ptr()->get_type().get())) {
          //structs are same type -> no more checks needed
          //annotate node with result type
          n->set_type(l_op->get_symbol_ptr()->get_type());
          n->set_isLval(false);
        }
        else {
          //structs are different types -> error
          SemanticError::raise(n->get_loc(), "Semantic Error: Illegal binary expr (assignment) - differing struct types");
        }
      }
      else {
        SemanticError::raise(n->get_loc(), "Semantic Error: Illegal assignment");
      }
      break;
    }

    //RELATIONAL OPERATORS && LOGICAL OPERATORS
    // Only works for both op = numeric (integral)
    // result type always int
    case TOK_LOGICAL_OR:
    case TOK_LOGICAL_AND:
    case TOK_INEQUALITY:
    case TOK_EQUALITY:
    case TOK_GTE:
    case TOK_GT:
    case TOK_LTE:
    case TOK_LT: {
      if(l_op_t -> is_integral() && r_op_t->is_integral()) {
        //Call helper function
        //Handles promotions, conversions.
        bin_exp_N_N(n);
        //lastly the result node is annotated with type int
        std::shared_ptr<Type> basicTypePtr(new BasicType(BasicTypeKind::INT, true));
        n->set_type(basicTypePtr);
        n->set_isLval(false);
      }
      else {
        SemanticError::raise(n->get_loc(), "Semantic Error: Illegal (relational/logical) binary expr  ");
      }
      break;
    }
    default: {
      SemanticError::raise(n->get_loc(), "Semantic Error: Unknown binary expr");
    }
  }
  //printf("EXIT BINARY EXPRESSION\n");
}

void SemanticAnalysis::visit_unary_expression(Node *n) {
  //(1) Operand must be numeric (integral)
  //(2) Operand must be promoted to int (or unsigned int) if less precise
  //(3) Node must be annotated with result type
  //    For ! result type is always int
  //    For - result type is type of op
  //    For ~ result type is type of op (not necessary to implement)
  // Pointer address of and dereference is also unary expressions
  //    For & (address of):
  //      Operand must be LValue
  //      Yields pointer to LValue's storage in mem
  //    For * (dereference):
  //      Only applied to pointer value
  //      Yields LValue with type = pointer base type

  visit(n->get_kid(1));

  auto op = n->get_kid(0);
  auto op_tag = op->get_tag();
  auto operand = n->get_kid(1);

  //Do (3)
  switch (op_tag) {
    case TOK_MINUS:
    case TOK_BITWISE_COMPL: {
      //Check (1)
      if(not operand->get_type()->is_integral()) {
        SemanticError::raise(n->get_loc(), "Semantic Error: Unary expression on non-numeric type");
      }
      //Do (2)
      if(operand->get_type()->get_basic_type_kind() < BasicTypeKind::INT) {
        operand = promote_to_int(operand);
        n->set_kid(1, operand);
      }
      //DO (3):
      n->set_type(operand->get_type());
      n->set_isLval(false); //unary expr not an Lval
      break;
    }
    case TOK_NOT: {
      //Check (1):
      if(not operand->get_type()->is_integral()) {
        SemanticError::raise(n->get_loc(), "Semantic Error: Unary expression on non-numeric type");
      }
      //Do (2):
      if(operand->get_type()->get_basic_type_kind() < BasicTypeKind::INT) {
        operand = promote_to_int(operand);
        n->set_kid(1, operand);
      }
      //DO (3):
      std::shared_ptr<Type> basicTypePtr(new BasicType(BasicTypeKind::INT, operand->get_type()->is_signed()));
      n->set_type(basicTypePtr);
      n->set_isLval(false); //unary expr not an Lval
      break;
    }
    //Address-of (need LVAL) (Yield pointer with LVAL base type)
    case TOK_AMPERSAND: {
      if(not operand->get_isLval()) {
        SemanticError::raise(n->get_loc(), "SemanticError: Address of on non-LVal (unary expr)");
      }
      std::shared_ptr<Type> PointerTypePtr(new PointerType(operand->get_type()));
      n->set_type(PointerTypePtr);
      n->set_isLval(false); //Address-of not LVAL
      //Set the symbol of the operand to be taken (address of) (used for codegen)
      if(operand->has_symbol()) {
        operand->get_symbol_ptr()->set_isTaken(true);
      }
      break;
    }
    //Dereference (need pointer) (Yield LVAL with pointer base type)
    case TOK_ASTERISK: {
      if(not operand->get_type()->is_pointer()) {
        SemanticError::raise(n->get_loc(), "SemanticError: Dereference on non-pointer (unary expr)");
      }
      n->set_type(operand->get_type()->get_base_type());
      n->set_isLval(true); //Dereferenced pointer is LVAL
      break;
    }
    default: {
      SemanticError::raise(n->get_loc(), "Semantic Error: Unary expression operator error");
    }
  }
}

//This is ++ and --
//NOT SUPPORTED (explicit in Operator section of assignment)
void SemanticAnalysis::visit_postfix_expression(Node *n) {
  SemanticError::raise(n->get_loc(), "incr/decr operation not supported");
}

//This is ternary expression
//WRONG FORMAT: (logical_or_expression TOK_QUESTION assignment_expression TOK_COLON conditional_expression)
//Last conditional expr should be assignment_expression
//NOT SUPPORTED
void SemanticAnalysis::visit_conditional_expression(Node *n) {
  SemanticError::raise(n->get_loc(), "Ternary expr not supported");
}

//Casts such as (short), (int), (unsigned int)
//AST IS WRONG - MISSING VARREF NODE
//Varref node needed to check if the cast var can be legally cast
//NOT SUPPORTED
void SemanticAnalysis::visit_cast_expression(Node *n) {
  SemanticError::raise(n->get_loc(), "Cast expression not supported");
}

//Cases such as func(x,y,z)
//When calling an instance of a function
void SemanticAnalysis::visit_function_call_expression(Node *n) {
  //printf("FUNCTION CALL\n");
  //THE FOLLOWING MUST BE THE CASE:
  //(1) The function has been declared/defined (can be found in symboltable)
  //(2) Number of args in call == number of args in function symboltable
  //(3) Type of args must also be the same

  //Then do:
  //(4) Set type of result node = function return type, set isLval = false

  //Visit children (AST_VARIABLE_REF), (AST_ARGUMENT_EXPRESSION_LIST)
  auto func = n->get_kid(0);
  auto arg_list = n->get_kid(1);
  visit(func); //CHECK (1) - visiting varref will check if in symboltable
  visit(arg_list);
  //CHECK (1) - Error if not Function
  if(not (func->get_symbol_ptr()->get_kind() == SymbolKind::FUNCTION)) {
    SemanticError::raise(n->get_loc(), "Semantic error: Illegal Function call (non-func type)");
  }
  //CHECK (2):
  //Number of params in func must equal number of kids in param list
  if(func->get_symbol_ptr()->get_type()->get_num_members() != arg_list->get_num_kids()) {
    SemanticError::raise(n->get_loc(), "Semantic error: Illegal Function call (Wrong param num)");
  }
  //CHECK (3):
  //Loop through all args in func and all kids in param list
  //Compare types
  auto func_symtab_name = "function " + func->get_symbol_ptr()->get_name();
  auto func_symtab = get_symtab(func_symtab_name);
  if(func_symtab == nullptr) {
    SemanticError::raise(n->get_loc(), "SemanticError: No associated Symboltable found to defined/declared func");
  }
  for(unsigned i = 0; i < arg_list->get_num_kids(); ++i) {
    auto arg_type = arg_list->get_kid(i)->get_type();
    auto param_type = func_symtab->get_entry(i)->get_type();
    if(arg_type->is_array()) {
      std::shared_ptr<Type> pointerTypeptr(new PointerType(arg_type->get_base_type()));
      arg_type = pointerTypeptr;
    }
    if(not arg_type->is_same(param_type.get())) {
      if(arg_type->is_integral() && param_type->is_integral()) {
        //These are the cases where we need to implicitly promote our argument
        //The alternative (demoting/truncating) an argument does not need a
        //Dedicated node.
        if(arg_type->get_basic_type_kind() < param_type->get_basic_type_kind()) {
          auto basic_type = param_type->get_basic_type_kind();
          switch (basic_type) {
            case BasicTypeKind::SHORT: {
              arg_list->set_kid(i, promote_to_short(arg_list->get_kid(i)));
              break;
            }
            case BasicTypeKind::INT: {
              arg_list->set_kid(i, promote_to_int(arg_list->get_kid(i)));
              break;
            }
            case BasicTypeKind::LONG: {
              arg_list->set_kid(i, promote_to_long(arg_list->get_kid(i)));
              break;
            }
            default: {
              break;
            }
          }
        }
      }
      else {
        SemanticError::raise(n->get_loc(), "Semantic error: Illegal Function call (parameter typing)");
      }
    }
  }

  //DO (4)
  n->set_isLval(false);
  n->set_type(func->get_symbol_ptr()->get_type()->get_base_type());
}

//Cases such as node.x
//Visiting a field of a struct
void SemanticAnalysis::visit_field_ref_expression(Node *n) {
  //MUST BE DONE:
  //(1). Check that struct instance in symboltable
  //(2). Check that struct type of instance has field with given name
  //(3). Get type of struct field with this name. Set node type.
  //(4). Field of a struct is LVAL. Set node LVAL = true.

  auto structure = n->get_kid(0);
  auto ident = n->get_kid(1);
  auto name = ident->get_str();
  //CHECK (1):
  visit(structure);
  if(not structure->get_type()->is_struct()) {
    SemanticError::raise(n->get_loc(), "SemanticError: Field ref expression not struct");
  }
  //CHECK (2):
  bool name_found = false;
  auto STR = structure->get_type();
  for(unsigned i = 0; i < STR->get_num_members();i++) {
    if(STR->get_member(i).get_name() == name) {
      name_found = true;
      auto field_type = STR->get_member(i).get_type();
      if(field_type->is_array()) {
        std::shared_ptr<Type> pointerTypeptr(new PointerType(field_type->get_base_type()));
        field_type = pointerTypeptr;
      }
      n->set_type(field_type); //DO (3):
      n->set_isLval(true); //DO (4):
    }
  }
  if(name_found == false) {
    //If we have looked through all members in struct and none matched the name
    SemanticError::raise(n->get_loc(), "SemanticError: Struct has no such field");
  }
}

//Cases such as node->x
//Visiting a field of a pointer to struct
void SemanticAnalysis::visit_indirect_field_ref_expression(Node *n) {
  //MUST BE DONE:
  //(1). Check that pointer to struct instance in symboltable
  //(2). Check that struct type of instance has field with given name
  //(3). Get type of struct field with this name. Set node type.
  //(4). Field reference of a struct is LVAL. Set node LVAL = true.

  auto struc_ptr = n->get_kid(0);
  auto ident = n->get_kid(1);
  auto name = ident->get_str();

  //CHECK (1):
  visit(struc_ptr); //check that something with same name as struc_ptr is in symboltable
  //Ensure that what is in fact in symboltable is pointer with base type struct.
  if(not (struc_ptr->get_type()->is_pointer() && struc_ptr->get_type()->get_base_type()->is_struct())) {
    SemanticError::raise(n->get_loc(), "SemanticError: Indirect Field ref expression type error");
  }
  //CHECK (2):
  bool name_found = false;
  auto STR = struc_ptr->get_type()->get_base_type();
  for(unsigned i = 0; i < STR->get_num_members();i++) {
    if(STR->get_member(i).get_name() == name) {
      name_found = true;
      n->set_type(STR->get_member(i).get_type()); //DO (3):
      n->set_isLval(true); //DO (4):
    }
  }
  if(name_found == false) {
    //If we have looked through all members in struct and none matched the name
    SemanticError::raise(n->get_loc(), "SemanticError: Struct has no such field");
  }
}

//Cases such as x[0] = 10;
//x must be array or pointer
void SemanticAnalysis::visit_array_element_ref_expression(Node *n) {
  //MUST BE THE CASE THAT:
  //(1): array/pointer must be in symboltable
  //DO:
  //(3): Set node type = array basetype (pointer basetype)
  //(4): Set Node isLval = true
  auto op = n->get_kid(0);
  auto index = n->get_kid(1);

  visit(op); //CHECK (1) - Variable_ref checks if name in symboltable
  visit(index);

  if(index->get_type()->get_basic_type_kind() != BasicTypeKind::INT &&
          index->get_type()->get_basic_type_kind() != BasicTypeKind::LONG) {
    SemanticError::raise(n->get_loc(), "SemanticError: Indexing using non-integer/non-long");
  }

  //If index basic type kind is int, we need to promote the int to a long
  //a[i] = *(a+i)   ->   since a is a pointer (long), i needs to be promoted
  if(index->get_type()->get_basic_type_kind() == BasicTypeKind::INT) {
    n->set_kid(1, promote_to_long(index));
  }

  //ARRAY, POINTER OR SOMETHING ELSE?
  if(op->get_type()->is_array()) {
    //DO (3),(4).
    n->set_type(op->get_type()->get_base_type()); //node type = array base type
    n->set_isLval(true); //node isLVal = true
  }
  else if(op->get_type()->is_pointer()) {
    //DO (3),(4).
    n->set_type(op->get_type()->get_base_type()); //node type = pointer base type
    n->set_isLval(true);
  }
  else {
    //CHECK (1): Check if arr_type is arrayType OR if it is pointer
    SemanticError::raise(n->get_loc(), "SemanticError: Indexing on non-array/pointer is illegal");
  }
}

//Lookup variable in symbol table -> error if not found
//Have node point to symbol
//Have node isLval = true (variable reference is lval)
void SemanticAnalysis::visit_variable_ref(Node *n) {
  // When visiting a variable reference we should:
  // 1. Lookup the associated value in the symbol table
  // 2. Annotate the node with pointer to symbol
  // 3. Set node Lval true (variable references are Lvalues)
  auto ident = n->get_kid(0)->get_str();
  auto symbol = m_cur_symtab->lookup_recursive(ident); // (1)
  if(symbol != nullptr){
    n->set_symbol(symbol);  //(2)
    n->set_isLval(true);    //(3)
  }
  else {
    SemanticError::raise(n->get_loc(), "Semantic Error: Invalid Variable Reference");
  }

}

//Annotate Node with Literal Value
//Annotate Node with type
void SemanticAnalysis::visit_literal_value(Node *n) {
  //printf("LITERAL VALUE\n");
  // When visiting literal value:
  // Use LiteralValue class
  // Annotate Node with type & Literal Value
  auto tok_lit = n->get_kid(0);
  auto tok_tag = tok_lit->get_tag();
  LiteralValue litVal;
  switch(tok_tag) {
    case TOK_INT_LIT: {
      //printf("LITERAL VALUE INT\n");
      //Type of Int literal is either INT, unsigned INT, LONG or unsigned LONG
      litVal = LiteralValue::from_int_literal(tok_lit->get_str(),tok_lit->get_loc());
      auto isUnsigned = litVal.is_unsigned();
      auto isLONG = litVal.is_long();
      if (isLONG) {
        std::shared_ptr<Type> basicTypePtr(new BasicType(BasicTypeKind::LONG, not isUnsigned));
        n->set_type(basicTypePtr);
        n->set_litVal(litVal);
      }
      else {
        //printf("LITERAL VALUE INT2\n");
        std::shared_ptr<Type> basicTypePtr(new BasicType(BasicTypeKind::INT, not isUnsigned));
        n->set_type(basicTypePtr);
        n->set_litVal(litVal);
        //printf("LITERAL VALUE INT3\n");
      }
      break;
    }
    case TOK_STR_LIT: {
      //Type of string literal is const char * (pointer to const char)
      litVal = LiteralValue::from_str_literal(tok_lit->get_str(),tok_lit->get_loc());
      std::shared_ptr<Type> basicTypePtr(new BasicType(BasicTypeKind::CHAR, true));
      std::shared_ptr<Type> QualifiedTypePtr(new QualifiedType(basicTypePtr, TypeQualifier::CONST));
      std::shared_ptr<Type> PointerTypePtr(new PointerType(QualifiedTypePtr));
      n->set_type(PointerTypePtr);
      n->set_litVal(litVal);
      break;
    }
    case TOK_CHAR_LIT: {
      //Type of character literal is INT
      litVal = LiteralValue::from_char_literal(tok_lit->get_str(),tok_lit->get_loc());
      std::shared_ptr<Type> basicTypePtr(new BasicType(BasicTypeKind::INT, false));
      n->set_type(basicTypePtr);
      n->set_litVal(litVal);
      break;
    }
    case TOK_FP_LIT: {
      SemanticError::raise(n->get_loc(), "Floating point values not supported");
    }
    default: {
      SemanticError::raise(n->get_loc(), "Type Error: Visit Literal Value");
    }
  }
  //printf("EXIT LITERAL VALUE\n");
}


// HELPER FUNCTIONS
SymbolTable *SemanticAnalysis::enter_scope(const std::string &name) {
  SymbolTable *symtab = new SymbolTable(m_cur_symtab, name);
  m_all_symtabs.push_back(symtab);
  m_cur_symtab = symtab;
  return symtab;
}

void SemanticAnalysis::leave_scope() {
  assert(m_cur_symtab->get_parent() != nullptr);
  m_cur_symtab = m_cur_symtab->get_parent();
}

//Promote to int and also call implicit_conversion to make an
//Explicit implicit conversion node.
Node *SemanticAnalysis::promote_to_int(Node *n) {
  assert(n->get_type()->is_integral());
  if(n->get_type()->get_basic_type_kind() < BasicTypeKind::INT) {
    std::shared_ptr<Type> type = std::make_shared<BasicType>(BasicTypeKind::INT, n->get_type()->is_signed());
    return implicit_conversion(n, type);
  }
  else {
    return n;
  }
}

//Promote to short and also call implicit_conversion to make an
//Explicit implicit conversion node.
Node *SemanticAnalysis::promote_to_short(Node *n) {
  assert(n->get_type()->is_integral());
  if(n->get_type()->get_basic_type_kind() < BasicTypeKind::SHORT) {
    std::shared_ptr<Type> type = std::make_shared<BasicType>(BasicTypeKind::SHORT, n->get_type()->is_signed());
    return implicit_conversion(n, type);
  }
  else {
    return n;
  }
}

//Promote to long and also call implicit_conversion to make an
//Explicit implicit conversion node.
Node *SemanticAnalysis::promote_to_long(Node *n) {
  assert(n->get_type()->is_integral());
  std::shared_ptr<Type> type = std::make_shared<BasicType>(BasicTypeKind::LONG, n->get_type()->is_signed());
  return implicit_conversion(n, type);
}

//convert to unsigned
Node *SemanticAnalysis::convert_to_unsigned(Node *n) {
  assert(n->get_type()->is_integral());
  std::shared_ptr<Type> type = std::make_shared<BasicType>(n->get_type()->get_basic_type_kind(), not n->get_type()->is_signed());
  return implicit_conversion(n, type);
}

//Promote to long and also call implicit_conversion to make an
//Explicit implicit conversion node.
Node *SemanticAnalysis::convert_to_left_type(Node *n) {
  assert(n->get_kid(1)->get_type()->is_integral());
  auto l_op = n->get_kid(1);
  auto r_op = n->get_kid(2);
  std::shared_ptr<Type> Ltype = std::make_shared<BasicType>(l_op->get_type()->get_basic_type_kind(), l_op->get_type()->is_signed());
  return implicit_conversion(r_op, Ltype);
}

Node *SemanticAnalysis::implicit_conversion(Node *n, std::shared_ptr<Type> type) {
  //printf("IMPLICIT CONVERSION\n");
  std::unique_ptr<Node> conversion(new Node(AST_IMPLICIT_CONVERSION, {n}));
  conversion->set_type(type);
  return conversion.release();
}

//Helper function for binary expression with two Numeric operands
void SemanticAnalysis::bin_exp_N_N(Node *n) {
  //printf("BIN_EXP_N_N USED\n");
  auto l_op = n->get_kid(1);
  auto r_op = n->get_kid(2);
  //1. Make sure both operands are at least as precise as INT
  if(l_op->get_type()->get_basic_type_kind() < BasicTypeKind::INT) {
    l_op = promote_to_int(l_op);
    n->set_kid(1, l_op );
  }
  if(r_op->get_type()->get_basic_type_kind() < BasicTypeKind::INT) {
    r_op = promote_to_int(r_op);
    n->set_kid(2, r_op );
  }
  //2. If one operand is more precise than the other, promote the other
  if(l_op->get_type()->get_basic_type_kind() > r_op->get_type()->get_basic_type_kind()) {
    r_op = promote_to_long(r_op);
    n->set_kid(2, r_op );
  }
  else if(r_op->get_type()->get_basic_type_kind() > l_op->get_type()->get_basic_type_kind()) {
    l_op = promote_to_long(l_op);
    n->set_kid(1, l_op );
  }
  //3. If the operands differ in signedness, the signed operand is implicitly converted to unsigned
  if((l_op->get_type()->is_signed()) && (not r_op->get_type()->is_signed())) {
    //l_op is converted to unsigned:
    l_op = convert_to_unsigned(l_op);
    n->set_kid(1, l_op );
  }
  if((not l_op->get_type()->is_signed()) && (r_op->get_type()->is_signed())) {
    //r_op is converted to unsigned:
    r_op = convert_to_unsigned(r_op);
    n->set_kid(2, r_op );
  }
  //printf("EXIT BIN_EXP_N_N\n");
}


