#pragma once

#include "../theory_solver.h"
#include <unordered_set>

namespace OptiSMT {

    // 位向量理论求解器
    class BitVectorSolver : public TheorySolver {
    private:
        std::unordered_map<std::string, NodePtr> declared_variables_;
        std::unordered_map<std::string, size_t> variable_widths_;  // 位向量宽度
        
    public:
        BitVectorSolver() = default;
        ~BitVectorSolver() override = default;
        
        // 实现基类接口
        TransformationResult transformConstraint(NodePtr constraint) override;
        TransformationResult transformConstraints(const std::vector<NodePtr>& constraints) override;
        
        // 变量处理
        bool declareVariable(const std::string& name, NodePtr var_node) override;
        std::vector<std::string> getVariables() const override;
        std::string getVariableType(const std::string& name) const override;
        
        // BigM方法支持
        double computeBigM(NodePtr constraint) override;
        bool supportsBigM() const override { return true; }
        
        // 辅助方法
        bool canHandle(NodePtr node) const override;
        std::string getTheoryName() const override { return "BitVector"; }
        void reset() override;
        
        // 预处理
        NodePtr preprocessConstraint(NodePtr constraint) override;
        bool simplifyConstraint(NodePtr& constraint) override;
        
    private:
        // 位向量转换方法
        std::string transformBitVectorTerm(NodePtr term);
        std::string transformBitVectorConstraint(NodePtr constraint);
        std::string transformBitVectorComparison(NodePtr constraint);
        
        // 位操作转换
        std::string transformBitVectorAnd(NodePtr node);
        std::string transformBitVectorOr(NodePtr node);
        std::string transformBitVectorXor(NodePtr node);
        std::string transformBitVectorNot(NodePtr node);
        std::string transformBitVectorShift(NodePtr node);
        std::string transformBitVectorExtract(NodePtr node);
        std::string transformBitVectorConcat(NodePtr node);
        
        // 算术操作转换
        std::string transformBitVectorAdd(NodePtr node);
        std::string transformBitVectorSub(NodePtr node);
        std::string transformBitVectorMul(NodePtr node);
        std::string transformBitVectorDiv(NodePtr node);
        
        // 比较操作转换
        std::string transformBitVectorUnsignedLess(NodePtr node);
        std::string transformBitVectorSignedLess(NodePtr node);
        
        // 位向量编码方法
        std::vector<std::string> encodeAsBinaryVariables(const std::string& bv_var, size_t width);
        std::string createBinaryConstraints(const std::vector<std::string>& binary_vars);
        
        // 辅助方法
        size_t getBitVectorWidth(NodePtr node) const;
        size_t getBitVectorWidth(const std::string& var_name) const;
        std::string getBitVectorConstantValue(NodePtr node) const;
        bool isBitVectorConstant(NodePtr node) const;
        
        // BigM特定方法
        double estimateBitVectorBounds(size_t width) const;
    };

} // namespace OptiSMT
