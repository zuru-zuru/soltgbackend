/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0


#pragma once


#include <libsolidity/formal/CHC.h>


namespace solidity::frontend
{


enum class RelOp { EQ, LT, GT, LE, GE };

class Invariant {
    public:
        const VariableDeclaration* var1;   
        const VariableDeclaration* var2;   
        bool isBoolean;            
        RelOp relop;          
        smtutil::Expression intConst;               
        bool boolVal;       
        bool isConst;           


        Invariant(const VariableDeclaration* v1, RelOp op, const VariableDeclaration* v2) 
            : var1(v1), var2(v2), isBoolean(false), relop(op), intConst((size_t)0), boolVal(false), isConst(false) {}

        Invariant(const VariableDeclaration* v1, RelOp op, smtutil::Expression constant) 
            : var1(v1), var2(nullptr), isBoolean(false), relop(op), intConst(constant), boolVal(false), isConst(true) {}

        Invariant(const VariableDeclaration* v1, bool b) 
            : var1(v1), var2(nullptr), isBoolean(true), relop(RelOp::EQ), intConst((size_t)0), boolVal(b), isConst(true) {}
};


class CandidateStore {
	public:
		ContractDefinition const* contract = nullptr;
		FunctionDefinition const* function = nullptr;
        Statement const* loop = nullptr;
		Predicate const* precondition = nullptr;
		Predicate const* header = nullptr;
        std::vector<Invariant> candidates;
        std::vector<const Predicate *> precondition_targets;
        std::vector<const Predicate *> inductive_targets;
        std::set<const VariableDeclaration *> changed_vars;
        bool changed_state = false;

};

class CHCInv;

class InvariantHandler {
    public:
        void addConstant(smtutil::Expression);
        void resetConstants();
        void generateCandidates(std::vector<Invariant> &_invs, std::set<const VariableDeclaration*> &);
        void testPrecondition(const Predicate& _precondition_block, std::vector<Invariant> &candidates, std::vector<Invariant> &proved);
        void testInductive(smtutil::Expression & _precondition_block, const Predicate& _header_block, const Predicate& _inductive_block, std::vector<Invariant> &candidates, std::vector<Invariant> &proved);
        void testPreconditionNew(std::vector<Invariant> &candidates, std::vector<const Predicate *> &targetsPre, std::vector<const Predicate *> &targetsInd);
        void testInductiveNew(smtutil::Expression & _precondition_block, const Predicate& _header_block, std::vector<Invariant> &candidates, std::vector<const Predicate *> &targets);
        void generatePreconditionTargets(const Predicate& _precondition_block, std::vector<Invariant> &candidates, std::vector<const Predicate *> &targets);
        void generateInductiveTargets(const Predicate& _inductive_block, std::vector<Invariant> &candidates, std::vector<const Predicate *> &targets);
        void setEncoder(CHCInv*);
        void save_invariants(std::vector<Invariant> &invariants, const Statement* loop);
        smtutil::Expression get_saved_invariants(const Statement* loop);
        bool check_saved_invariants(const Statement* loop);
    private:
        std::vector<smtutil::Expression> m_constants;
        CHCInv* m_encoder;
        smtutil::Expression invariantToExpression(Invariant _inv); 
        smtutil::Expression invariantToExpression(const VariableDeclaration* var1, RelOp op, const VariableDeclaration* var2);
        smtutil::Expression invariantToExpression(const VariableDeclaration* var1, RelOp op, smtutil::Expression intConst);

        std::map<const Statement*, std::vector<Invariant>> m_saved_invariants;
};



class CHCInv: public CHC
{
    public: 
    	CHCInv(
		smt::EncodingContext& _context,
		langutil::UniqueErrorReporter& _errorReporter,
		langutil::UniqueErrorReporter& _unsupportedErrorReporter,
		langutil::ErrorReporter& _provedSafeReporter,
		std::map<util::h256, std::string> const& _smtlib2Responses,
		ReadCallback::Callback const& _smtCallback,
		ModelCheckerSettings _settings,
		langutil::CharStreamProvider const& _charStreamProvider
	);
        std::unique_ptr<smtutil::CHCSolverInterface> invariant_solver_interface;
        virtual void analyze(SourceUnit const& _sources) override;
        friend class InvariantHandler;

    private:
        bool firstPass;
        bool saveConstants = false;
        void analyzeFirstPass(SourceUnit const& _sources);
        virtual void resetSourceAnalysis() override;
        std::map<const Statement*, bool> loop_invariants_generated;
        bool source_invariants_generated = false;
        void resetSourceInvariantAnalysis() ;

        bool visit(WhileStatement const&) override;
        bool visit(ForStatement const&) override;

        bool visitWhile(WhileStatement const&);
        bool visitDoWhile(WhileStatement const&);
        bool visitFor(ForStatement const&);

        void endVisit(Literal const&);

        smtutil::Expression invariant();

        Predicate const* createInvariantSymbolicBlock(smtutil::SortPointer _sort, std::string const& _name, PredicateType _predType, ASTNode const* _node = nullptr, ContractDefinition const* _contractContext = nullptr);
        void createInvariantCheckerBlock();
        Predicate const* m_InvariantPredicate = nullptr;
        void connectBlocksInvariant(smtutil::Expression const& _from, smtutil::Expression const& _to, smtutil::Expression const& _constraints = smtutil::Expression(true));
        
        InvariantHandler m_invariant_checker;
	    std::vector<CandidateStore> InvariantTargets;
};




}
