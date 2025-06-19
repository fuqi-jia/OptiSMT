#include "theory_solver.h"
#include <iostream>

namespace OptiSMT {

// 静态成员变量定义
size_t TheorySolver::aux_var_counter_ = 0;

// 实现通用的辅助方法
std::string TheorySolver::generateAuxiliaryVariableName() {
    return "aux_var_" + std::to_string(++aux_var_counter_);
}

std::string TheorySolver::nodeToString(NodePtr node) {
    if (!node) {
        return "null";
    }
    
    if (node->isVar()) {
        return node->getName();
    }
    
    if (node->isConst()) {
        return node->getName();
    }
    
    // 简化的节点转字符串实现
    return "node_" + std::to_string(static_cast<int>(node->getKind()));
}

bool TheorySolver::isLinearTerm(NodePtr node) {
    if (!node) {
        return true;
    }
    
    // 变量和常数是线性的
    if (node->isVar() || node->isConst()) {
        return true;
    }
    
    // 加法、减法、负号是线性的
    if (node->isAdd() || node->isSub() || node->isNeg()) {
        for (size_t i = 0; i < node->getChildrenSize(); ++i) {
            if (!isLinearTerm(node->getChild(i))) {
                return false;
            }
        }
        return true;
    }
    
    // 乘法：检查是否至多有一个变量
    if (node->isMul()) {
        bool has_variable = false;
        for (size_t i = 0; i < node->getChildrenSize(); ++i) {
            auto child = node->getChild(i);
            if (child && child->isVar()) {
                if (has_variable) {
                    return false;  // 多个变量相乘，非线性
                }
                has_variable = true;
            }
        }
        return true;
    }
    
    return false;
}

bool TheorySolver::containsVariable(NodePtr node, const std::string& var_name) {
    if (!node) {
        return false;
    }
    
    if (node->isVar() && node->getName() == var_name) {
        return true;
    }
    
    for (size_t i = 0; i < node->getChildrenSize(); ++i) {
        if (containsVariable(node->getChild(i), var_name)) {
            return true;
        }
    }
    
    return false;
}

} // namespace OptiSMT 