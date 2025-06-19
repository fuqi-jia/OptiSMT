#include "la.h"
#include <iostream>
#include <sstream>

namespace OptiSMT {

// LinearArithmeticSolver 实现
TransformationResult LinearArithmeticSolver::transformConstraint(NodePtr constraint) {
    TransformationResult result;
    
    if (!constraint) {
        result.error_message = "Null constraint";
        return result;
    }
    
    if (!canHandle(constraint)) {
        result.error_message = "Cannot handle this constraint type";
        return result;
    }
    
    try {
        if (constraint->isArithComp()) {
            std::string transformed = transformArithmeticConstraint(constraint);
            if (!transformed.empty()) {
                result.linear_constraints.push_back(transformed);
                result.success = true;
            }
        } else if (constraint->isVBool() || constraint->isCBool()) {
            std::string transformed = transformBooleanConstraint(constraint);
            if (!transformed.empty()) {
                result.linear_constraints.push_back(transformed);
                result.success = true;
            }
        } else {
            // 默认处理
            result.linear_constraints.push_back("default_constraint");
            result.success = true;
        }
    } catch (const std::exception& e) {
        result.error_message = "Exception during transformation: " + std::string(e.what());
    }
    
    return result;
}

TransformationResult LinearArithmeticSolver::transformConstraints(const std::vector<NodePtr>& constraints) {
    TransformationResult combined_result;
    combined_result.success = true;
    
    for (const auto& constraint : constraints) {
        auto result = transformConstraint(constraint);
        if (result.success) {
            // 合并结果
            combined_result.linear_constraints.insert(
                combined_result.linear_constraints.end(),
                result.linear_constraints.begin(),
                result.linear_constraints.end()
            );
            combined_result.auxiliary_variables.insert(
                combined_result.auxiliary_variables.end(),
                result.auxiliary_variables.begin(),
                result.auxiliary_variables.end()
            );
        } else {
            combined_result.success = false;
            combined_result.error_message += result.error_message + "; ";
        }
    }
    
    return combined_result;
}

bool LinearArithmeticSolver::declareVariable(const std::string& name, NodePtr var_node) {
    if (name.empty() || !var_node) {
        return false;
    }
    
    declared_variables_[name] = var_node;
    
    // 根据变量类型分类
    if (var_node->isVInt()) {
        integer_variables_.insert(name);
    } else if (var_node->isVReal()) {
        real_variables_.insert(name);
    }
    
    return true;
}

std::vector<std::string> LinearArithmeticSolver::getVariables() const {
    std::vector<std::string> variables;
    for (const auto& [name, node] : declared_variables_) {
        variables.push_back(name);
    }
    return variables;
}

std::string LinearArithmeticSolver::getVariableType(const std::string& name) const {
    if (integer_variables_.count(name)) {
        return "integer";
    } else if (real_variables_.count(name)) {
        return "real";
    }
    return "unknown";
}

double LinearArithmeticSolver::computeBigM(NodePtr constraint) {
    if (!constraint) {
        return 1e6;  // 默认值
    }
    
    // 简化的BigM计算
    std::unordered_set<std::string> vars;
    collectVariables(constraint, vars);
    
    double estimated_bound = 1000.0;  // 保守估计
    for (const auto& var : vars) {
        estimated_bound = std::max(estimated_bound, estimateVariableBounds(var));
    }
    
    return estimated_bound * 10;  // 保守的BigM值
}

bool LinearArithmeticSolver::canHandle(NodePtr node) const {
    if (!node) {
        return false;
    }
    
    // 检查是否是线性算术表达式
    if (node->isArithComp() || node->isArithTerm()) {
        return isLinearExpression(node);
    }
    
    // 布尔变量也可以处理
    if (node->isVBool() || node->isCBool()) {
        return true;
    }
    
    return false;
}

void LinearArithmeticSolver::reset() {
    declared_variables_.clear();
    integer_variables_.clear();
    real_variables_.clear();
}

NodePtr LinearArithmeticSolver::preprocessConstraint(NodePtr constraint) {
    if (!constraint) {
        return constraint;
    }
    
    // 简化的预处理
    std::cout << "Preprocessing linear arithmetic constraint" << std::endl;
    return constraint;
}

bool LinearArithmeticSolver::simplifyConstraint(NodePtr& constraint) {
    if (!constraint) {
        return false;
    }
    
    std::cout << "Simplifying linear arithmetic constraint" << std::endl;
    return true;
}

// 私有方法实现
std::string LinearArithmeticSolver::transformLinearTerm(NodePtr term) {
    if (!term) {
        return "0";
    }
    
    if (term->isVar()) {
        return term->getName();
    }
    
    if (term->isConst()) {
        return term->getName();
    }
    
    if (term->isAdd()) {
        std::ostringstream oss;
        for (size_t i = 0; i < term->getChildrenSize(); ++i) {
            if (i > 0) oss << " + ";
            oss << transformLinearTerm(term->getChild(i));
        }
        return oss.str();
    }
    
    if (term->isSub()) {
        std::ostringstream oss;
        oss << transformLinearTerm(term->getChild(0));
        for (size_t i = 1; i < term->getChildrenSize(); ++i) {
            oss << " - " << transformLinearTerm(term->getChild(i));
        }
        return oss.str();
    }
    
    if (term->isMul()) {
        std::ostringstream oss;
        for (size_t i = 0; i < term->getChildrenSize(); ++i) {
            if (i > 0) oss << " * ";
            oss << transformLinearTerm(term->getChild(i));
        }
        return oss.str();
    }
    
    if (term->isNeg()) {
        return "- " + transformLinearTerm(term->getChild(0));
    }
    
    return "unknown_term";
}

std::string LinearArithmeticSolver::transformArithmeticConstraint(NodePtr constraint) {
    if (!constraint || constraint->getChildrenSize() < 2) {
        return "";
    }
    
    std::string left = transformLinearTerm(constraint->getChild(0));
    std::string right = transformLinearTerm(constraint->getChild(1));
    std::string op;
    
    if (constraint->isLe()) {
        op = "<=";
    } else if (constraint->isLt()) {
        op = "<";
    } else if (constraint->isGe()) {
        op = ">=";
    } else if (constraint->isGt()) {
        op = ">";
    } else if (constraint->isEq()) {
        op = "=";
    } else {
        return "";
    }
    
    return left + " " + op + " " + right;
}

std::string LinearArithmeticSolver::transformComparisonConstraint(NodePtr constraint) {
    return transformArithmeticConstraint(constraint);
}

std::string LinearArithmeticSolver::transformBooleanConstraint(NodePtr constraint) {
    if (!constraint) {
        return "";
    }
    
    if (constraint->isTrue()) {
        return "1 = 1";  // 恒真约束
    }
    
    if (constraint->isFalse()) {
        return "1 = 0";  // 恒假约束
    }
    
    if (constraint->isVBool()) {
        // 布尔变量，需要添加 0 <= var <= 1 约束
        std::string var_name = constraint->getName();
        return var_name + " >= 0; " + var_name + " <= 1";
    }
    
    return "boolean_constraint";
}

bool LinearArithmeticSolver::isLinearExpression(NodePtr expr) const {
    if (!expr) {
        return true;
    }
    
    // 变量和常数是线性的
    if (expr->isVar() || expr->isConst()) {
        return true;
    }
    
    // 加法、减法、负号是线性的
    if (expr->isAdd() || expr->isSub() || expr->isNeg()) {
        for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
            if (!isLinearExpression(expr->getChild(i))) {
                return false;
            }
        }
        return true;
    }
    
    // 乘法：检查是否至多有一个变量
    if (expr->isMul()) {
        bool has_variable = false;
        for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
            auto child = expr->getChild(i);
            if (child && child->isVar()) {
                if (has_variable) {
                    return false;  // 多个变量相乘，非线性
                }
                has_variable = true;
            } else if (child && !child->isConst()) {
                // 非常数、非变量的表达式
                if (!isLinearExpression(child)) {
                    return false;
                }
            }
        }
        return true;
    }
    
    // 比较运算
    if (expr->isArithComp()) {
        for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
            if (!isLinearExpression(expr->getChild(i))) {
                return false;
            }
        }
        return true;
    }
    
    return false;
}

std::string LinearArithmeticSolver::linearExpressionToString(NodePtr expr) {
    return transformLinearTerm(expr);
}

std::string LinearArithmeticSolver::transformWithBigM(NodePtr constraint, const std::string& indicator_var) {
    double big_m = computeBigM(constraint);
    std::string base_constraint = transformArithmeticConstraint(constraint);
    
    // 添加BigM项
    // 例如：x <= 5 变成 x <= 5 + M * (1 - indicator)
    return base_constraint + " + " + std::to_string(big_m) + " * (1 - " + indicator_var + ")";
}

std::string LinearArithmeticSolver::createBooleanVariableConstraints(const std::string& bool_var) {
    return bool_var + " >= 0; " + bool_var + " <= 1";
}

void LinearArithmeticSolver::collectVariables(NodePtr node, std::unordered_set<std::string>& vars) const {
    if (!node) {
        return;
    }
    
    if (node->isVar()) {
        vars.insert(node->getName());
    }
    
    for (size_t i = 0; i < node->getChildrenSize(); ++i) {
        collectVariables(node->getChild(i), vars);
    }
}

double LinearArithmeticSolver::estimateVariableBounds(const std::string& var_name) const {
    // 简化的边界估计
    if (integer_variables_.count(var_name)) {
        return 1000.0;  // 整数变量的保守估计
    } else if (real_variables_.count(var_name)) {
        return 1000.0;  // 实数变量的保守估计
    }
    return 100.0;
}

bool LinearArithmeticSolver::isIntegerVariable(const std::string& name) const {
    return integer_variables_.count(name) > 0;
}

} // namespace OptiSMT
