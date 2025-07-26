NAME          SMT2LP
ROWS
 N  OBJ
 G  C0
 G  C1
 L  C2
 G  C3
COLUMNS
    MARK0001  'MARKER'                 'INTORG'
    y  OBJ       0
    MARK0001  'MARKER'                 'INTEND'
    y  C1       1
    y  C2       1
    y  C3       1
    MARK0001  'MARKER'                 'INTORG'
    x  OBJ       0
    MARK0001  'MARKER'                 'INTEND'
    x  C0       1
    x  C2       1
    x  C3       2
RHS
    RHS1      C0       -0
    RHS1      C1       -0
    RHS1      C2       10
    RHS1      C3       5
BOUNDS
 MI BOUND1    y
 MI BOUND1    x
ENDATA
