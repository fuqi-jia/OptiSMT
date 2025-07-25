#!/bin/bash

# OptiSMT 简洁构建脚本

echo "=== OptiSMT: SMT到线性程序转换器 ==="
echo "使用大M方法处理OR约束，生成LP/MPS文件"
echo ""

# 创建build目录
echo "创建构建目录..."
mkdir -p build
cd build

echo "=== 运行CMake配置 ==="
cmake ..

if [ $? -ne 0 ]; then
    echo "❌ CMake配置失败！"
    exit 1
fi

echo "=== 编译项目 ==="
make -j$(nproc)

if [ $? -ne 0 ]; then
    echo "❌ 编译失败！"
    exit 1
fi

echo "✅ 编译成功！"
echo ""
echo "可执行文件位置: ./optismt"
echo ""

# 检查examples目录是否存在
if [ ! -d "../examples" ]; then
    echo "⚠️  examples目录不存在，创建示例目录和文件..."
    mkdir -p ../examples
    
    # 创建一个简单的测试示例
    cat > ../examples/simple_or.smt2 << 'EOF'
(declare-fun x () Real)
(declare-fun y () Real)
(assert (or (>= x 5) (<= y 3)))
(assert (>= (+ x y) 1))
(check-sat)
EOF

    cat > ../examples/complex_or.smt2 << 'EOF'
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Int)
(assert (and (>= a 0) (<= a 10)))
(assert (and (>= b 0) (<= b 10)))
(assert (and (>= c 0) (<= c 5)))
(assert (or (>= a 7) (>= b 8) (>= c 3)))
(assert (<= (+ a b c) 20))
(check-sat)
EOF

    echo "已创建示例文件: examples/simple_or.smt2, examples/complex_or.smt2"
fi

# 获取examples目录中的SMT文件
SMT_FILES=(../examples/*.smt2)

if [ ${#SMT_FILES[@]} -eq 0 ] || [ ! -f "${SMT_FILES[0]}" ]; then
    echo "❌ examples目录中没有找到.smt2文件！"
    exit 1
fi

echo "=== 运行测试示例 ==="
echo "发现 ${#SMT_FILES[@]} 个SMT文件"
echo ""

# 遍历所有SMT文件
for smt_file in "${SMT_FILES[@]}"; do
    if [ -f "$smt_file" ]; then
        filename=$(basename "$smt_file" .smt2)
        echo "🔄 处理文件: $(basename "$smt_file")"
        echo "命令: ./optismt -v -o ../examples/$filename $smt_file"
        echo "----------------------------------------"
        
        ./optismt -v -o "../examples/$filename" "$smt_file"
        
        if [ $? -eq 0 ]; then
            echo "----------------------------------------"
            echo "✅ 成功处理 $(basename "$smt_file")"
            echo "生成的文件:"
            ls -la "../examples/$filename".{lp,mps} 2>/dev/null || echo "  (文件可能在其他位置)"
            echo ""
        else
            echo "❌ 处理 $(basename "$smt_file") 失败！"
            echo ""
        fi
    fi
done

echo "=== 测试完成 ==="
echo "生成的所有文件:"
ls -la ../examples/*.{lp,mps} 2>/dev/null || echo "没有找到生成的LP/MPS文件"
echo ""

echo "使用方法:"
echo "  ./optismt <SMT文件>              # 转换SMT文件为LP/MPS"
echo "  ./optismt -h                     # 显示帮助信息"
echo "  ./optismt -v example.smt2        # 详细输出模式"
echo "  ./optismt -o output example.smt2 # 指定输出文件前缀" 