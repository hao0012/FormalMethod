from typing import List
import unittest
from dataclasses import dataclass

from z3 import *

from counter import counter


##################################
# The abstract syntax for the Tac (three address code) language:
"""
S ::= x=y | x=y+z | x=y-z | x=y*z | x=y/z
F ::= f(x1, ..., xn){S;* return x;}
"""

# expression
@dataclass
class Exp:
    pass
@dataclass
class ExpVar(Exp):
    x: str
@dataclass
class ExpBop(Exp):
    x: str
    y: str
    bop: str

# statement
@dataclass
class Stm:
    pass
@dataclass
class StmAssign(Stm):
    x: str
    e: Exp

# function:
@dataclass
class Function:
    name: str
    args: List[str]
    stms: List[Stm]
    ret: str

###############################################
# pretty printer
def pp_exp(e: Exp):
  match e:
    case ExpVar(x):
      return x
    case ExpBop(x, y, bop):
      return f"{x} {bop} {y}"

def pp_stm(s: Stm):
  match s:
    case StmAssign(x, e):
      return f"{x} = {pp_exp(e)}"

def func_format(f: Function):
  match f:
    case Function(name, args, stms, ret):
      s = f"{name}("
      for i in range(len(args) - 1):
        s += f"{args[i]}, "
      s += args[-1]
      s += "){\n"
      for stm in stms:
        s += f"\t{pp_stm(stm)};\n"
      s += f"\treturn {ret};\n"
      s += "}"
      return s
  return ""
def pp_func(f: Function):
  print(func_format(f))


###############################################
# SSA conversion:

# Exercise 7: Finish the SSA conversion function `to_ssa_stmt()`
# take a function 'f', convert it to SSA
def to_ssa_exp(e: Exp, var_map, fresh_var) -> Exp:
  match e:
    case ExpVar(x):
      return ExpVar(var_map[x])
    case ExpBop(x, y, bop):
      return ExpBop(var_map[x], var_map[y], bop)

def to_ssa_stm(s: Stm, var_map, fresh_var) -> Stm:
  match s:
    case StmAssign(x, e):
      var_map[x] = next(fresh_var)
      return StmAssign(var_map[x], to_ssa_exp(e, var_map, fresh_var))

def to_ssa_func(f: Function) -> Function:
    var_map = {arg: arg for arg in f.args}
    fresh_var = counter(prefix=f"tac_{f.name}")
    new_stmts = [to_ssa_stm(s, var_map, fresh_var) for s in f.stms]
    return Function(f.name,
                    f.args,
                    new_stmts,
                    var_map[f.ret])
    

    


###############################################
# Exercise 8-1: Finished the `gen_cons_stmt` function to generate 
# constraints form TAC statements
# Generate Z3 constraints:
def gen_con_exp(e: Exp) -> BoolRef:
    match e:
      case ExpVar(x):
        return Const(x, DeclareSort('S'))
      case ExpBop(left, right, bop):
        func_name = "f_" + bop
        left = gen_con_exp(ExpVar(left))
        right = gen_con_exp(ExpVar(right))
        return z3.Function(func_name,
                           DeclareSort('S'),
                           DeclareSort('S'),
                           DeclareSort('S')).__call__(left, right)

def gen_cons_stm(s: Stm) -> BoolRef:
    match s:
      case StmAssign(x, e):
        return Const(x, DeclareSort('S')).__eq__(gen_con_exp(e))


# Exercise 8-2: Finished the `gen_cons_stmt` function to 
# generate constraints form TAC function 
def gen_cons_func(f: Function) -> List[BoolRef]:
    return [gen_cons_stm(stm) for stm in f.stms]


###############################################
# Tests

test_case = Function('f',
                     ['s1', 's2', 't1', 't2'],
                     [StmAssign('a', ExpBop('s1', 't1', "+")),
                      StmAssign('b', ExpBop('s2', 't2', "+")),
                      StmAssign('c', ExpBop('a', 'b', "*")),
                      StmAssign('b', ExpBop('c', 's1', "*")),
                      StmAssign('z', ExpVar('b'))],
                     'z')


if __name__ == '__main__':
    # should print: 
    # f(s1, s2, t1, t2){
    #   a = s1 + t1;
    #   b = s2 + t2;
    #   c = a * b;
    #   b = c * s1;
    #   z = b;
    #   return z;
    # }
    pp_func(test_case)
    
    ssa = to_ssa_func(test_case)
    # should print:
    # f(s1, s2, t1, t2){
    #   _tac_f_0 = s1 + t1;
    #   _tac_f_1 = s2 + t2;
    #   _tac_f_2 = _tac_f_0 * _tac_f_1;
    #   _tac_f_3 = _tac_f_2 * s1;
    #   _tac_f_4 = _tac_f_3;
    #   return _tac_f_4;
    # }
    pp_func(ssa)
    
    cons = gen_cons_func(ssa)
    
    # should has constraints:
    # [_tac_f_0 == f_add(s1, t1),
    #  _tac_f_1 == f_add(s2, t2),
    #  _tac_f_2 == f_mul(_tac_f_0, _tac_f_1),
    #  _tac_f_3 == f_mul(_tac_f_2, s1),
    #  _tac_f_4 == _tac_f_3]
    print(cons)
