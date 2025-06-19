#pragma once

#include "parser.h"
#include <memory>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <functional>
#include <chrono>

using SMTParser::NodePtr;
using SMTParser::ParserPtr;

// 前向声明
namespace SMTParser {
    class DAGNode;
    class Parser;
    class Objective;
}

namespace OptiSMT {
    // 类型别名
    using NodePtr = std::shared_ptr<SMTParser::DAGNode>;
    using ParserPtr = std::shared_ptr<SMTParser::Parser>;
    
    // 常用常量
    constexpr double DEFAULT_BIG_M = 1e6;
    constexpr double DEFAULT_PRECISION = 1e-10;
    constexpr double INFINITY_VALUE = 1e20;
    
    // 前向声明
    class TheorySolver;
    class LinearArithmeticSolver;
    class BitVectorSolver;
    class NonlinearArithmeticSolver; 
    class FloatingPointSolver;
    class OptimizationBackend_Base;
    class SMTToOptTransformer;
    class OptiSMTSolver;
}