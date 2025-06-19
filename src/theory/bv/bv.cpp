#include "bv.h"
#include <iostream>
#include <cmath>

namespace OptiSMT {

TransformationResult BitVectorSolver::transformConstraint(NodePtr constraint) {
    TransformationResult result;
    result.success = true;
    result.linear_constraints.push_back("bitvector_constraint_placeholder");
    return result;
}

TransformationResult BitVectorSolver::transformConstraints(const std::vector<NodePtr>& constraints) {
    TransformationResult result;
    result.success = true;
    for (size_t i = 0; i < constraints.size(); ++i) {
        result.linear_constraints.push_back("bv_constraint_" + std::to_string(i));
    }
    return result;
}

bool BitVectorSolver::declareVariable(const std::string& name, NodePtr var_node) {
    declared_variables_[name] = var_node;
    if (var_node && var_node->isVBV()) {
        variable_widths_[name] = getBitVectorWidth(var_node);
    }
    return true;
}

std::vector<std::string> BitVectorSolver::getVariables() const {
    std::vector<std::string> vars;
    for (const auto& [name, node] : declared_variables_) {
        vars.push_back(name);
    }
    return vars;
}

std::string BitVectorSolver::getVariableType(const std::string& name) const {
    return "bitvector";
}

double BitVectorSolver::computeBigM(NodePtr constraint) {
    // 对于位向量，BigM通常基于位宽
    size_t max_width = 32;  // 默认宽度
    return std::pow(2.0, max_width) - 1;
}

bool BitVectorSolver::canHandle(NodePtr node) const {
    return node && (node->isBVTerm() || node->isBvAtom() || node->isVBV() || node->isCBV());
}

void BitVectorSolver::reset() {
    declared_variables_.clear();
    variable_widths_.clear();
}

NodePtr BitVectorSolver::preprocessConstraint(NodePtr constraint) {
    std::cout << "Preprocessing bitvector constraint" << std::endl;
    return constraint;
}

bool BitVectorSolver::simplifyConstraint(NodePtr& constraint) {
    std::cout << "Simplifying bitvector constraint" << std::endl;
    return true;
}

size_t BitVectorSolver::getBitVectorWidth(NodePtr node) const {
    if (!node) return 32;  // 默认宽度
    
    // 这里应该从节点的sort信息中获取位宽
    // 简化实现
    return 32;
}

size_t BitVectorSolver::getBitVectorWidth(const std::string& var_name) const {
    auto it = variable_widths_.find(var_name);
    if (it != variable_widths_.end()) {
        return it->second;
    }
    return 32;  // 默认宽度
}

} // namespace OptiSMT
