#!/bin/bash

# OptiSMT 构建和测试脚本

echo "=== OptiSMT 构建和测试脚本 ==="

# 创建build目录
mkdir -p build
cd build

echo "=== 运行CMake配置 ==="
cmake ..

if [ $? -ne 0 ]; then
    echo "CMake配置失败！"
    exit 1
fi

echo "=== 编译项目 ==="
make -j4

if [ $? -ne 0 ]; then
    echo "编译失败！"
    exit 1
fi

echo "=== 编译成功！==="

echo "=== 测试简单线性问题 ==="
echo "运行: ./optismt ../examples/simple_linear.smt2"
echo "----------------------------------------"
./optismt ../examples/simple_linear.smt2
echo "----------------------------------------"

echo "=== 测试完成 ===" 