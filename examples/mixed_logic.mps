NAME          SMT2LP
ROWS
 N  OBJ
 G  C0
 G  C1
 L  C2
 L  C3
 L  C4
 G  C5
COLUMNS
    b2  OBJ       0
    MARK0001  'MARKER'                 'INTORG'
    b2  OBJ       0
    MARK0001  'MARKER'                 'INTEND'
    b1  OBJ       0
    MARK0001  'MARKER'                 'INTORG'
    b1  OBJ       0
    MARK0001  'MARKER'                 'INTEND'
    y  OBJ       0
    y  C1       1
    y  C3       1
    y  C4       1
    MARK0001  'MARKER'                 'INTORG'
    y  OBJ       0
    MARK0001  'MARKER'                 'INTEND'
    x  OBJ       0
    x  C0       1
    x  C2       1
    x  C4       1
    MARK0001  'MARKER'                 'INTORG'
    x  OBJ       0
    MARK0001  'MARKER'                 'INTEND'
RHS
    RHS1      C0       -0
    RHS1      C1       -0
    RHS1      C2       20
    RHS1      C3       20
    RHS1      C4       25
    RHS1      C5       1
BOUNDS
 BV BOUND1    b2
 BV BOUND1    b1
 MI BOUND1    y
 MI BOUND1    x
ENDATA
