#pragma once

#include "parser.h"
#include <memory>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <iostream>
#include <sstream>

// 使用SMT Parser的类型
using SMTParser::NodePtr;
using SMTParser::ParserPtr;

namespace OptiSMT {
    // 基本数据结构
    constexpr double DEFAULT_BIG_M = 1e6;
    
    // 变量类型
    enum class VariableType {
        REAL,     // 实数变量
        INTEGER,  // 整数变量 
        BINARY    // 0-1变量
    };
    
    // 约束类型
    enum class ConstraintType {
        LINEAR_EQ,    // 线性等式 ax = b
        LINEAR_LE,    // 线性不等式 ax <= b
        LINEAR_GE,    // 线性不等式 ax >= b
        OR_CLAUSE     // 析取约束 (c1 || c2 || ...)
    };
    
    // 变量信息
    struct Variable {
        std::string name;
        VariableType type;
        double lower_bound = -1e20;
        double upper_bound = 1e20;
        
        Variable(const std::string& n, VariableType t) : name(n), type(t) {}
    };
    
    // 线性项: 系数 * 变量
    struct LinearTerm {
        SMTParser::Number coefficient;
        std::string variable;
        
        LinearTerm(SMTParser::Number coeff, const std::string& var) 
            : coefficient(coeff), variable(var) {}
    };
    
    // 线性约束: sum(coeff_i * var_i) op rhs
    struct LinearConstraint {
        std::vector<LinearTerm> terms;
        ConstraintType type;
        SMTParser::Number rhs;  // 右侧常数
        
        LinearConstraint(ConstraintType t, SMTParser::Number r) : type(t), rhs(r) {}
        
        void addTerm(SMTParser::Number coeff, const std::string& var) {
            terms.emplace_back(coeff, var);
        }
    };
    
    // OR约束：多个线性约束的析取
    struct OrConstraint {
        std::vector<LinearConstraint> clauses;
        
        void addClause(const LinearConstraint& clause) {
            clauses.push_back(clause);
        }
    };
}