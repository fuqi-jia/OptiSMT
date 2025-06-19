;; 混合逻辑问题示例
;; 包含布尔变量和算术约束

(set-logic QF_LIA)
(set-info :source |OptiSMT Example: Mixed Integer Logic|)

;; 声明变量
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)

;; 基本边界约束
(assert (>= x 0))
(assert (>= y 0))
(assert (<= x 20))
(assert (<= y 20))

;; 条件约束：如果 b1 为真，则 x >= 10
(assert (=> b1 (>= x 10)))

;; 条件约束：如果 b2 为真，则 y >= 15
(assert (=> b2 (>= y 15)))

;; 逻辑约束：b1 和 b2 不能同时为真
(assert (not (and b1 b2)))

;; 至少一个布尔变量必须为真
(assert (or b1 b2))

;; 算术约束
(assert (<= (+ x y) 25))

(check-sat)
(get-model) 