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

    private:
        virtual void resetSourceAnalysis() override;
        virtual void addRule(smtutil::Expression const& _rule, std::string const& _ruleName) override;
        virtual Predicate const* createSymbolicBlock(smtutil::SortPointer _sort, std::string const& _name, PredicateType _predType, ASTNode const* _node = nullptr, ContractDefinition const* _contractContext = nullptr) override;
        Predicate const* createInvariantSymbolicBlock(smtutil::SortPointer _sort, std::string const& _name, PredicateType _predType, ASTNode const* _node = nullptr, ContractDefinition const* _contractContext = nullptr);
        void endVisit(IndexRangeAccess const& _node) override;
        void createInvariantCheckerBlock();
        Predicate const* m_InvariantPredicate = nullptr;
        void connectBlocksInvariant(smtutil::Expression const& _from, smtutil::Expression const& _to, smtutil::Expression const& _constraints = smtutil::Expression(true));
};

}
