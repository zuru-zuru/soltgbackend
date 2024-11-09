#include <libsolidity/formal/CHCInv.h>

#include <libsolidity/formal/ModelChecker.h>

#ifdef HAVE_Z3
#include <libsmtutil/Z3CHCInterface.h>
#endif

#include <libsolidity/formal/ArraySlicePredicate.h>
#include <libsolidity/formal/EldaricaCHCSmtLib2Interface.h>
#include <libsolidity/formal/Invariants.h>
#include <libsolidity/formal/PredicateInstance.h>
#include <libsolidity/formal/PredicateSort.h>
#include <libsolidity/formal/SymbolicTypes.h>

#include <libsolidity/ast/TypeProvider.h>

#include <libsmtutil/CHCSmtLib2Interface.h>
#include <liblangutil/CharStreamProvider.h>
#include <libsolutil/Algorithms.h>
#include <libsolutil/StringUtils.h>

#ifdef HAVE_Z3_DLOPEN
#include <z3_version.h>
#endif

#include <boost/algorithm/string.hpp>

#include <range/v3/algorithm/for_each.hpp>
#include <range/v3/view.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/reverse.hpp>

#include <charconv>
#include <queue>

using namespace solidity;
using namespace solidity::util;
using namespace solidity::langutil;
using namespace solidity::smtutil;
using namespace solidity::frontend;
using namespace solidity::frontend::smt;


CHCInv::CHCInv(
	EncodingContext& _context,
	UniqueErrorReporter& _errorReporter,
	UniqueErrorReporter& _unsupportedErrorReporter,
	ErrorReporter& _provedSafeReporter,
	std::map<util::h256, std::string> const& _smtlib2Responses,
	ReadCallback::Callback const& _smtCallback,
	ModelCheckerSettings _settings,
	CharStreamProvider const& _charStreamProvider
):
    CHC(_context, _errorReporter, _unsupportedErrorReporter, _provedSafeReporter, _smtlib2Responses, _smtCallback, _settings, _charStreamProvider)
{
	std::cout << "Invariant generation in CHC encoding enabled!\n";
}


void CHCInv::resetSourceAnalysis()
{
    std::cout << "resetSourceAnalysis\n";
    invariant_solver_interface = std::make_unique<Z3CHCInterface>(m_settings.timeout);
	CHC::resetSourceAnalysis();
    return;
}

void CHCInv::endVisit(IndexRangeAccess const& _range)
{
	createExpr(_range);

	auto baseArray = std::dynamic_pointer_cast<SymbolicArrayVariable>(m_context.expression(_range.baseExpression()));
	auto sliceArray = std::dynamic_pointer_cast<SymbolicArrayVariable>(m_context.expression(_range));
	solAssert(baseArray && sliceArray, "");

	auto const& sliceData = ArraySlicePredicate::create(sliceArray->sort(), m_context);
	if (!sliceData.first)
	{
		for (auto pred: sliceData.second.predicates){
			m_interface->registerRelation(pred->functor());
            invariant_solver_interface->registerRelation(pred->functor());
        }
		for (auto const& rule: sliceData.second.rules)
			addRule(rule, "");
	}

	auto start = _range.startExpression() ? expr(*_range.startExpression()) : 0;
	auto end = _range.endExpression() ? expr(*_range.endExpression()) : baseArray->length();
	auto slicePred = (*sliceData.second.predicates.at(0))({
		baseArray->elements(),
		sliceArray->elements(),
		start,
		end
	});

	m_context.addAssertion(slicePred);
	m_context.addAssertion(sliceArray->length() == end - start);
}

Predicate const* CHCInv::createSymbolicBlock(SortPointer _sort, std::string const& _name, PredicateType _predType, ASTNode const* _node, ContractDefinition const* _contractContext)
{
	auto const* block = Predicate::create(_sort, _name, _predType, m_context, _node, _contractContext, m_scopes);
	m_interface->registerRelation(block->functor());
    invariant_solver_interface->registerRelation(block->functor());
	return block;
}

Predicate const* CHCInv::createInvariantSymbolicBlock(SortPointer _sort, std::string const& _name, PredicateType _predType, ASTNode const* _node, ContractDefinition const* _contractContext)
{
	auto const* block = Predicate::create(_sort, _name, _predType, m_context, _node, _contractContext, m_scopes);
    invariant_solver_interface->registerRelation(block->functor());
	return block;
}

void CHCInv::addRule(smtutil::Expression const& _rule, std::string const& _ruleName)
{   
    std::cout << _ruleName << std::endl;
	m_interface->addRule(_rule, _ruleName);
    invariant_solver_interface->addRule(_rule, _ruleName);
}

void CHCInv::createInvariantCheckerBlock()
{
	m_InvariantPredicate = createInvariantSymbolicBlock(
		arity0FunctionSort(),
		"invariant_target_" + std::to_string(m_context.newUniqueId()),
		PredicateType::Error
	);
}



void CHCInv::connectBlocksInvariant(smtutil::Expression const& _from, smtutil::Expression const& _to, smtutil::Expression const& _constraints)
{
	smtutil::Expression edge = smtutil::Expression::implies(
		_from && _constraints,
		_to
	);
	invariant_solver_interface->addRule(edge, _from.name + "_to_" + _to.name);
}


void CHCInv::analyze(SourceUnit const& _source)
{
    CHC::analyze(_source);
    invariant_solver_interface->printEncoding();
}