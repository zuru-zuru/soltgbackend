#pragma once


#include <libsolidity/formal/EncodingContext.h>
#include <libsolidity/formal/ModelCheckerSettings.h>
#include <libsolidity/formal/SymbolicVariables.h>
#include <libsolidity/formal/VariableUsage.h>

#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/ASTVisitor.h>
#include <libsolidity/interface/ReadFile.h>
#include <liblangutil/UniqueErrorReporter.h>

#include <string>
#include <unordered_map>
#include <vector>
#include <utility>



namespace solidity::frontend
{
    class DependencyHandler {
	public:
        void reset();
        void activate();
        void deactivate();
        void setCurrentContract(const ContractDefinition*);
        void mapFunctionSummary(const FunctionDefinition*, std::string);
        void addFunctionToCurrentContract(const FunctionDefinition*);
        void addEdge(const FunctionDefinition*, const FunctionDefinition*);
        void addVariableAssignment(const VariableDeclaration*, const FunctionDefinition*);
        void addVariableUse(const VariableDeclaration*, const FunctionDefinition*);
        void addBalanceUse(const FunctionDefinition*);
        bool functionHasLoopOrRecursion(const FunctionDefinition*);
        bool functionHasBranch(const FunctionDefinition*);
        void setFunctionHasBranch(const FunctionDefinition*);
        void setFunctionHasLoopOrRecursion(const FunctionDefinition*);
        void printDependancyGraph();

        void processFirstPass();

	private:
		
        void dependancyUpdateOne(const FunctionDefinition * _func);
		void dependancyUpdateAll();
		// void callUpdate();
		bool checkEdge(const FunctionDefinition * _src, const FunctionDefinition * _dst);
        std::map<std::string, std::set<std::string>> getDependancyGraph(const ContractDefinition*);

        const ContractDefinition* m_current_contract;
        bool active = false;
        std::map<const ContractDefinition*, std::set<const FunctionDefinition*, frontend::ASTCompareByID<ASTNode>>> contract_funcs;
		std::map<const FunctionDefinition*, std::set<const FunctionDefinition*, frontend::ASTCompareByID<ASTNode>>> out_edges;
		std::map<const FunctionDefinition*, std::string, frontend::ASTCompareByID<ASTNode>> summary_clause;
		std::map<const FunctionDefinition*, std::set<const VariableDeclaration*, frontend::ASTCompareByID<ASTNode>>> modified_vars;  
		std::map<const FunctionDefinition*, std::set<const VariableDeclaration*, frontend::ASTCompareByID<ASTNode>>> used_vars;
        std::map<const FunctionDefinition*, bool> uses_balance;

        std::map<const FunctionDefinition*, bool> has_branch;
        std::map<const FunctionDefinition*, bool> has_loop_or_recursion; 
};

}