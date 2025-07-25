# OptiSMT - SMT到线性程序转换器

一个简洁清晰的工具，专门用于将SMT问题转换为线性程序，使用大M方法处理OR约束，生成LP和MPS格式文件。

## 核心功能

- ✅ 解析SMT-LIB2格式文件
- ✅ 使用**大M方法**将OR约束转换为线性约束
- ✅ 生成**LP格式**文件（可被Gurobi、CPLEX等求解器读取）
- ✅ 生成**MPS格式**文件（标准的数学规划格式）
- ✅ 简洁清晰的代码结构，易于扩展

## 快速开始

### 编译

```bash
# 使用构建脚本（推荐）
./build_and_test.sh

# 或手动使用CMake
mkdir build && cd build
cmake ..
make -j$(nproc)
```

### 基本使用

```bash
# 转换SMT文件，生成output.lp和output.mps
./optismt problem.smt2

# 指定输出文件前缀
./optismt -o result problem.smt2

# 设置大M值并显示详细信息
./optismt -m 10000 -v problem.smt2

# 只生成LP文件
./optismt --lp-only problem.smt2
```

### 示例

假设有SMT文件`example.smt2`：
```smt
(declare-fun x () Real)
(declare-fun y () Real)
(assert (or (>= x 5) (<= y 3)))
(assert (>= (+ x y) 1))
(check-sat)
```

运行：
```bash
./optismt -v example.smt2
```

输出：
```
=== OptiSMT: SMT到线性程序转换器 ===

步骤1: 解析SMT文件...
发现 2 个变量
发现 2 个约束
处理OR约束，子句数量: 2
转换完成：
  变量数量: 4
  线性约束: 1
  OR约束: 1

步骤2: 应用大M方法转换OR约束...
应用BigM方法转换 1 个OR约束
BigM转换完成，现有线性约束数量: 4

步骤3: 生成线性程序文件...
生成LP文件: output.lp
LP文件生成完成
生成MPS文件: output.mps
MPS文件生成完成

=== 转换完成 ===
已生成以下文件:
  output.lp (LP格式)
  output.mps (MPS格式)

可以使用商业求解器(如Gurobi、CPLEX)或开源求解器(如SCIP)求解这些文件。
```

## 命令行选项

```
用法: ./optismt [选项] <SMT文件>

选项:
  -h, --help           显示帮助信息
  -m, --big-m <值>     设置大M值 (默认: 1000000)
  -o, --output <文件>  输出文件前缀 (默认: output)
  --lp-only           只生成LP文件
  --mps-only          只生成MPS文件
  -v, --verbose       详细输出
```

## 技术特点

### 大M方法原理

对于OR约束 `(C1 || C2 || ... || Cn)`，我们引入二进制指示变量 `δ1, δ2, ..., δn`，并转换为：

1. `C1 + M*(1-δ1) >= 0`
2. `C2 + M*(1-δ2) >= 0`
3. `...`
4. `Cn + M*(1-δn) >= 0`
5. `δ1 + δ2 + ... + δn >= 1`

其中M是足够大的常数，确保当δi=0时对应约束自动满足。

### 支持的SMT特性

- 线性算术约束（=, <=, >=, <, >）
- OR逻辑连接符
- AND逻辑连接符
- 实数和整数变量
- 布尔变量（自动转换为0-1变量）

## 项目结构

```
OptiSMT/
├── src/
│   ├── common.h              # 基本数据结构
│   ├── smt_transformer.h     # 转换器接口
│   ├── smt_transformer.cpp   # 转换器实现
│   └── main.cpp             # 主程序
├── SMTParser/               # SMT解析器库（您的实现）
├── CMakeLists.txt           # CMake编译配置
├── build_and_test.sh        # 一键构建测试脚本
└── README.md               # 说明文档
```

## 后续扩展

这个简化版本为后续扩展提供了清晰的架构：

1. **API接口**：可在`smt_transformer.h`基础上添加C/Python API
2. **非线性处理**：可在`SMTTransformer`类中添加非线性约束处理
3. **其他求解器**：可添加直接调用Gurobi/CPLEX的接口
4. **优化目标**：可扩展支持最优化问题

## 许可证

MIT License - 可自由使用和修改
