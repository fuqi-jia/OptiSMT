#pragma once

#include "common.h"

namespace OptiSMT {
    
    // SMT到线性程序转换器
    class SMTTransformer {
    private:
        std::vector<Variable> variables_;                    // 所有变量
        std::vector<LinearConstraint> linear_constraints_;   // 线性约束
        std::vector<OrConstraint> or_constraints_;          // OR约束
        std::unordered_map<std::string, size_t> var_map_;   // 变量名到索引的映射
        
        double big_m_value_ = DEFAULT_BIG_M;                // BigM值
        size_t aux_var_counter_ = 0;                        // 辅助变量计数器
        
    public:
        SMTTransformer() = default;
        
        // 主要转换接口
        bool transformSMTFile(const std::string& filename);
        bool transformSMTConstraints(ParserPtr parser);
        
        // 大M方法转换OR约束
        void applyBigMTransformation();
        
        // 生成文件
        bool generateLPFile(const std::string& filename) const;
        bool generateMPSFile(const std::string& filename) const;
        
        // 配置
        void setBigM(double big_m) { big_m_value_ = big_m; }
        double getBigM() const { return big_m_value_; }
        
        // 获取结果
        const std::vector<Variable>& getVariables() const { return variables_; }
        const std::vector<LinearConstraint>& getLinearConstraints() const { return linear_constraints_; }
        size_t getVariableCount() const { return variables_.size(); }
        size_t getConstraintCount() const { return linear_constraints_.size(); }
        
        // 统计信息
        void printStatistics() const;
        
    private:
        // 内部转换方法
        bool processNode(NodePtr node);
        bool processOrNode(NodePtr node);
        bool processLinearConstraint(NodePtr node);
        bool extractLinearTerms(NodePtr node, std::vector<LinearTerm>& terms, SMTParser::Number& constant);
        bool extractLinearExpression(NodePtr node, std::vector<LinearTerm>& terms, SMTParser::Number& constant);
        
        // 变量管理
        std::string addVariable(const std::string& name, VariableType type);
        std::string generateAuxVariable();
        
        // 约束转换
        ConstraintType getConstraintType(NodePtr node);
        void addLinearConstraint(const std::vector<LinearTerm>& terms, ConstraintType type, SMTParser::Number rhs);
        
        // BigM转换
        void transformOrConstraint(const OrConstraint& or_constraint);
        
        // 文件生成辅助方法
        std::string formatLinearConstraint(const LinearConstraint& constraint) const;
        std::string formatVariable(const Variable& var) const;
    };
    
} // namespace OptiSMT 