from z3 import *
import set_functions

set_param(max_width=150)

s = Solver()

Z = IntSort()
f = Function("f", Z, Z)
x, y, z = Ints('x y z')
A = Array('A', Z, Z)
fml = Implies(x + 2 == y, f(Store(A, x, 3)[y - 2]) == f(y - x + 1))
solve(fml)

S = DeclareSort('S')
e = Const('e', S)
solve(ForAll(e, e != e))