# OptiSMT - SMT到优化问题转换求解器

OptiSMT是一个将SMT（可满足性模理论）问题转换为优化问题的求解器，支持调用多种优化后端（如Gurobi、CPLEX等）来求解转换后的问题。

## 特性

### 支持的理论
- **线性算术（Linear Arithmetic）**: 线性实数和整数约束
- **位向量（Bit Vectors）**: 固定宽度位向量操作
- **非线性算术（Nonlinear Arithmetic）**: 乘法、幂函数、超越函数等
- **浮点数（Floating Point）**: IEEE 754浮点数算术

### 支持的优化后端
- **Gurobi**: 商业优化求解器（推荐）
- **CPLEX**: IBM的商业优化求解器
- **Z3 Optimize**: Microsoft的开源SMT求解器优化功能
- **SCIP**: 开源混合整数规划求解器

### 转换技术
- **BigM方法**: 将逻辑约束转换为线性约束
- **分段线性逼近**: 处理非线性函数
- **McCormick包络**: 双线性项线性化
- **SOS约束**: 特殊有序集约束
- **指示器约束**: 条件约束处理

## 安装

### 依赖要求
- C++17编译器（GCC 7+, Clang 5+, MSVC 2019+）
- CMake 3.12+
- SMTParser库（作为子模块包含）

### 可选依赖
- Gurobi优化器（推荐安装）
- IBM CPLEX
- Z3求解器
- SCIP求解器

### 编译步骤

```bash
# 克隆项目
git clone --recursive https://github.com/your-org/OptiSMT.git
cd OptiSMT

# 创建构建目录
mkdir build && cd build

# 配置项目
cmake ..

# 编译
make -j$(nproc)

# 安装（可选）
sudo make install
```

### 配置Gurobi
如果您有Gurobi许可证：

```bash
export GUROBI_HOME=/path/to/gurobi
export LD_LIBRARY_PATH=$GUROBI_HOME/lib:$LD_LIBRARY_PATH
```

## 使用方法

### 基本使用

```bash
# 求解SMT文件
./optismt problem.smt2

# 使用特定后端
./optismt -b gurobi problem.smt2

# 设置时间限制
./optismt -t 300 problem.smt2

# 详细输出
./optismt -v problem.smt2

# 显示统计信息
./optismt -s problem.smt2
```

### 高级选项

```bash
# 禁用BigM方法
./optismt --no-big-m problem.smt2

# 自定义BigM值
./optismt -m 1000000 problem.smt2

# 导出优化模型
./optismt --dump-model model.lp problem.smt2

# 设置MIP间隙
./optismt -g 0.01 problem.smt2
```

## 示例

### 简单线性问题

```smt2
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 10))
(assert (>= (+ (* 2 x) y) 5))

(maximize (+ x y))
(check-sat)
(get-model)
```

### 非线性问题

```smt2
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)

(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ (* x x) (* y y)) 1.0))

(minimize (+ x y))
(check-sat)
(get-model)
```

### 位向量问题

```smt2
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(assert (bvugt x #x00))
(assert (bvult y #xFF))
(assert (= (bvand x y) #x0F))

(check-sat)
(get-model)
```

## API使用

### C++ API示例

```cpp
#include "optismt.h"

int main() {
    // 创建求解器
    auto solver = OptiSMT::createOptiSMTSolver(
        OptiSMT::OptimizationBackend::GUROBI
    );
    
    // 配置求解器
    solver->setUseBigM(true);
    solver->setDefaultBigM(1e6);
    solver->setTimeLimit(300.0);
    
    // 加载SMT文件
    if (!solver->loadSMTFile("problem.smt2")) {
        std::cerr << "无法加载文件" << std::endl;
        return 1;
    }
    
    // 求解
    auto result = solver->solve();
    
    // 检查结果
    if (result == OptiSMT::SolverResult::SAT) {
        std::cout << "SAT" << std::endl;
        
        // 获取模型
        std::unordered_map<std::string, double> model;
        if (solver->getModel(model)) {
            for (const auto& [var, value] : model) {
                std::cout << var << " = " << value << std::endl;
            }
        }
    }
    
    return 0;
}
```

## 架构设计

### 主要组件

1. **SMTParser**: 前端解析器，解析SMT-LIB2格式文件
2. **TheorySolver**: 理论求解器，处理不同理论的约束
3. **SMTToOptTransformer**: 转换器，将SMT约束转换为优化约束
4. **OptimizationBackend**: 后端接口，支持多种优化求解器
5. **OptiSMTSolver**: 主求解器，协调各组件工作

### 转换流程

```
SMT文件 → SMTParser → 理论分析 → 约束转换 → 优化模型 → 后端求解 → 结果
```

## 性能调优

### BigM方法优化
- 使用自适应BigM值计算
- 避免过大的BigM值导致数值问题
- 考虑使用指示器约束替代BigM

### 预处理技术
- 约束简化和合并
- 变量边界推导
- 冗余约束消除

### 后端选择
- 线性问题：优先使用Gurobi或CPLEX
- 非线性问题：考虑SCIP或特殊处理
- 位向量问题：可能需要特殊编码技术

## 限制和已知问题

1. **浮点数精度**: 浮点数运算可能引入舍入误差
2. **非线性近似**: 非线性函数的线性化可能不够精确
3. **内存使用**: 大型问题可能需要大量内存
4. **求解时间**: 复杂问题的转换和求解可能很慢

## 贡献指南

欢迎贡献代码！请遵循以下步骤：

1. Fork项目
2. 创建特性分支
3. 提交更改
4. 推送到分支
5. 创建Pull Request

## 许可证

本项目采用MIT许可证。详见LICENSE文件。

## 联系方式

- 项目主页: https://github.com/your-org/OptiSMT
- 问题报告: https://github.com/your-org/OptiSMT/issues
- 邮箱: optismt@example.com

## 引用

如果您在研究中使用了OptiSMT，请引用：

```bibtex
@misc{optismt2025,
  title={OptiSMT: A Tool for Transforming SMT Problems to Optimization Problems},
  author={OptiSMT Development Team},
  year={2025},
  url={https://github.com/your-org/OptiSMT}
}
``` 