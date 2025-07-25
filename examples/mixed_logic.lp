\* SMT到LP转换生成的线性程序 *\

Minimize
obj: 0

Subject To
c0: x >= -0
c1: y >= -0
c2: x <= 20
c3: y <= 20
c4: x + y <= 25
c5:  >= 1

Bounds
0 <= b2 <= 1
0 <= b1 <= 1
y free
x free

General
y
x

Binary
b2
b1

End
