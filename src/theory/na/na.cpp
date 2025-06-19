#include "na.h"
#include <iostream>

namespace OptiSMT {

TransformationResult NonlinearArithmeticSolver::transformConstraint(NodePtr constraint) {
    TransformationResult result;
    result.success = true;
    result.linear_constraints.push_back("nonlinear_constraint_placeholder");
    return result;
}

TransformationResult NonlinearArithmeticSolver::transformConstraints(const std::vector<NodePtr>& constraints) {
    TransformationResult result;
    result.success = true;
    for (size_t i = 0; i < constraints.size(); ++i) {
        result.linear_constraints.push_back("na_constraint_" + std::to_string(i));
    }
    return result;
}

bool NonlinearArithmeticSolver::declareVariable(const std::string& name, NodePtr var_node) {
    declared_variables_[name] = var_node;
    if (var_node && var_node->isVInt()) {
        integer_variables_.insert(name);
    } else if (var_node && var_node->isVReal()) {
        real_variables_.insert(name);
    }
    return true;
}

std::vector<std::string> NonlinearArithmeticSolver::getVariables() const {
    std::vector<std::string> vars;
    for (const auto& [name, node] : declared_variables_) {
        vars.push_back(name);
    }
    return vars;
}

std::string NonlinearArithmeticSolver::getVariableType(const std::string& name) const {
    if (integer_variables_.count(name)) {
        return "integer";
    } else if (real_variables_.count(name)) {
        return "real";
    }
    return "unknown";
}

double NonlinearArithmeticSolver::computeBigM(NodePtr constraint) {
    return 1e6;  // 简化的BigM计算
}

bool NonlinearArithmeticSolver::canHandle(NodePtr node) const {
    return node && (isNonlinearExpression(node) || 
                   containsMultiplication(node) || 
                   containsTranscendentalFunction(node));
}

void NonlinearArithmeticSolver::reset() {
    declared_variables_.clear();
    integer_variables_.clear();
    real_variables_.clear();
}

NodePtr NonlinearArithmeticSolver::preprocessConstraint(NodePtr constraint) {
    std::cout << "Preprocessing nonlinear arithmetic constraint" << std::endl;
    return constraint;
}

bool NonlinearArithmeticSolver::simplifyConstraint(NodePtr& constraint) {
    std::cout << "Simplifying nonlinear arithmetic constraint" << std::endl;
    return true;
}

void NonlinearArithmeticSolver::setLinearizationPrecision(double precision) {
    linearization_precision_ = precision;
}

void NonlinearArithmeticSolver::setMaxPiecewiseSegments(size_t segments) {
    max_piecewise_segments_ = segments;
}

bool NonlinearArithmeticSolver::isNonlinearExpression(NodePtr expr) const {
    if (!expr) return false;
    
    // 检查乘法运算中是否有多个变量
    if (expr->isMul()) {
        int var_count = 0;
        for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
            auto child = expr->getChild(i);
            if (child && child->isVar()) {
                var_count++;
            }
        }
        return var_count > 1;  // 多个变量相乘是非线性的
    }
    
    // 检查是否包含幂运算、指数运算等
    return expr->isTranscendentalOp();
}

bool NonlinearArithmeticSolver::containsMultiplication(NodePtr expr) const {
    if (!expr) return false;
    
    if (expr->isMul()) {
        return true;
    }
    
    for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
        if (containsMultiplication(expr->getChild(i))) {
            return true;
        }
    }
    
    return false;
}

bool NonlinearArithmeticSolver::containsTranscendentalFunction(NodePtr expr) const {
    if (!expr) return false;
    
    return expr->isTranscendentalOp();
}

} // namespace OptiSMT
