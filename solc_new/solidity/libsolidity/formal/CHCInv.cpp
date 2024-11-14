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
	SMTEncoder::resetSourceAnalysis();

	m_unprovedTargets.clear();
	m_invariants.clear();
	m_functionTargetIds.clear();
	m_verificationTargets.clear();
	m_queryPlaceholders.clear();
	m_callGraph.clear();
	m_summaries.clear();
	m_externalSummaries.clear();
	m_interfaces.clear();
	m_nondetInterfaces.clear();
	m_constructorSummaries.clear();
	m_contractInitializers.clear();
	Predicate::reset();
	ArraySlicePredicate::reset();
	m_blockCounter = 0;
	
    solAssert(m_settings.solvers.smtlib2);

    m_interface = std::make_unique<CHCSmtLib2Interface>(m_smtlib2Responses, m_smtCallback, m_settings.timeout);

    auto smtlib2Interface = dynamic_cast<CHCSmtLib2Interface*>(m_interface.get());
    solAssert(smtlib2Interface);
    smtlib2Interface->reset();
    m_context.setSolver(smtlib2Interface);

	m_context.reset();
	m_context.resetUniqueId();
	m_context.setAssertionAccumulation(false);
}


void CHCInv::resetSourceInvariantAnalysis()
{
	SMTEncoder::resetSourceAnalysis();

	m_unprovedTargets.clear();
	m_invariants.clear();
	m_functionTargetIds.clear();
	m_verificationTargets.clear();
	m_queryPlaceholders.clear();
	m_callGraph.clear();
	m_summaries.clear();
	m_externalSummaries.clear();
	m_interfaces.clear();
	m_nondetInterfaces.clear();
	m_constructorSummaries.clear();
	m_contractInitializers.clear();
	Predicate::reset();
	ArraySlicePredicate::reset();
	m_blockCounter = 0;


    // z3::fixedpoint does not have a reset mechanism, so we need to create another.
    m_interface = std::make_unique<Z3CHCInterface>(m_settings.timeout);
    auto z3Interface = dynamic_cast<Z3CHCInterface const*>(m_interface.get());
    solAssert(z3Interface, "");
    m_context.setSolver(z3Interface->z3Interface());

	m_context.reset();
	m_context.resetUniqueId();
	m_context.setAssertionAccumulation(false);
}


void CHCInv::createInvariantCheckerBlock()
{
	m_InvariantPredicate = createSymbolicBlock(
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


void CHCInv::analyzeFirstPass(SourceUnit const& _source)
{
    std::cout << "chcinv analyze first pass called" << std::endl;

	if (!shouldAnalyze(_source))
		return;

    firstPass = true;
    m_dependency_handler.activate();

	resetSourceInvariantAnalysis();

	auto sources = sourceDependencies(_source);
	collectFreeFunctions(sources);
	createFreeConstants(sources);
	state().prepareForSourceUnit(_source, encodeExternalCallsAsTrusted());

	for (auto const* source: sources)
		defineInterfacesAndSummaries(*source);
	for (auto const* source: sources)
		source->accept(*this);

    // process function dependencies
    m_dependency_handler.processFirstPass();
    firstPass = false;
    m_dependency_handler.deactivate();
    saveConstants = false;
    return;
}


void CHCInv::analyze(SourceUnit const& _source)
{
    std::cout << "chcinv analyze called" << std::endl;
    
    analyzeFirstPass(_source);

	// At this point every enabled solver is available.
	if (!m_settings.solvers.eld && !m_settings.solvers.smtlib2 && !m_settings.solvers.z3)
	{
		m_errorReporter.warning(
			7649_error,
			SourceLocation(),
			"CHC analysis was not possible since no Horn solver was found and enabled."
			" The accepted solvers for CHC are Eldarica and z3."
		);
		return;
	}

	if (m_settings.solvers.eld && m_settings.solvers.z3)
		m_errorReporter.warning(
			5798_error,
			SourceLocation(),
			"Multiple Horn solvers were selected for CHC."
			" CHC only supports one solver at a time, therefore only z3 will be used."
			" If you wish to use Eldarica, please enable Eldarica only."
		);

	if (!shouldAnalyze(_source))
		return;
    
    InvariantTargets.clear();
	resetSourceInvariantAnalysis();

	auto sources = sourceDependencies(_source);
	collectFreeFunctions(sources);
	createFreeConstants(sources);
	state().prepareForSourceUnit(_source, encodeExternalCallsAsTrusted());

	for (auto const* source: sources)
		defineInterfacesAndSummaries(*source);
	for (auto const* source: sources)
		source->accept(*this);

    std::cout << InvariantTargets.size() << std::endl;
    for (auto target: InvariantTargets) {
		std::cout << "Invariant generation started" << std::endl;

		resetContractAnalysis();
		initContract(*target.contract);
		m_currentContract = target.contract;
		clearIndices(m_currentContract);

		m_scopes.push_back(m_currentContract);

		m_stateVariables = SMTEncoder::stateVariablesIncludingInheritedAndPrivate(*m_currentContract);


		m_scopes.push_back(target.function);

		initFunction(*target.function);
		m_currentFunction = target.function;

		setCurrentBlock(*target.precondition);

        // change variables
        for (auto var: target.changed_vars) {
            m_context.newValue(*var);
        }

        if (target.changed_state) {
            m_context.state().newState();
        }

        // test precondition
        m_invariant_checker.testPreconditionNew(target.candidates, target.precondition_targets, target.inductive_targets);
        // test inductive
        m_invariant_checker.testInductiveNew(m_currentBlock, *target.header, target.candidates, target.inductive_targets);
        // save invariants
        m_invariant_checker.save_invariants(target.candidates, target.loop);

		m_scopes.pop_back();
		m_currentFunction = nullptr;
        popCallStack();
		m_scopes.pop_back();

		m_context.resetAllVariables();

		if (m_callStack.empty()) m_context.popSolver();
		m_currentContract = nullptr;

		std::cout << "Invariant generation finished" << std::endl;

	}
    std::cout << "done generation" << std::endl;

    source_invariants_generated = true;

    m_settings.printQuery = true;
    m_settings.solvers.z3 = false;
    m_settings.solvers.smtlib2 = true;
    // std::cout << "Hello" << std::endl;

    CHC::analyze(_source);
}

bool CHCInv::visitDoWhile(WhileStatement const& _while) {
    return CHC::visit(_while);
}

bool CHCInv::visitWhile(WhileStatement const& _while) 
{
    int hasLoopOrRecursionPrev = hasLoopOrRecursion;
    hasLoopOrRecursion += 1;
    int hasBranchPrev = hasBranch;

	bool unknownFunctionCallWasSeen = m_unknownFunctionCallSeen;
	m_unknownFunctionCallSeen = false;

	solAssert(m_currentFunction, "");
	auto const& functionBody = m_currentFunction->body();

	std::string namePrefix = "while";
	auto loopHeaderBlock = createBlock(&_while, PredicateType::FunctionBlock, namePrefix + "_header_");
    // declare precondition test block
    auto preconditionTestBlock = createBlock(&_while, PredicateType::FunctionBlock, namePrefix + "_precondition_test_");
	auto loopBodyBlock = createBlock(&_while.body(), PredicateType::FunctionBlock, namePrefix + "_body_");
    // declare inductive test block
    auto inductiveTestBlock = createBlock(&_while, PredicateType::FunctionBlock, namePrefix + "_inductive_test_");
	auto afterLoopBlock = createBlock(&functionBody, PredicateType::FunctionBlock);

	auto outerBreakDest = m_breakDest;
	auto outerContinueDest = m_continueDest;
	m_breakDest = afterLoopBlock;
	m_continueDest = loopHeaderBlock;

    // connect to precondition test
    connectBlocks(m_currentBlock, predicate(*preconditionTestBlock));

    m_context.resetChangedVariables();

	setCurrentBlock(*loopHeaderBlock);
    // reset constants
    m_invariant_checker.resetConstants();
    saveConstants = true;
	_while.condition().accept(*this);
    saveConstants = false;
	auto condition = expr(_while.condition());
	connectBlocks(m_currentBlock, predicate(*loopBodyBlock), condition); 
	connectBlocks(m_currentBlock, predicate(*afterLoopBlock), !condition);

	// Loop body visit.
	setCurrentBlock(*loopBodyBlock);
	_while.body().accept(*this);

    m_breakDest = outerBreakDest;
	m_continueDest = outerContinueDest;

    // connect to inductive test block

    connectBlocks(m_currentBlock, predicate(*inductiveTestBlock));

    setCurrentBlock(*preconditionTestBlock);
    auto preconditionPredicate = predicate(*preconditionTestBlock);


    
    for (auto const* var: m_stateVariables) {
        m_context.changedValue(*var);        
    }
    for (auto const& var: m_currentFunction->parameters() + m_currentFunction->returnParameters()) {
        m_context.changedValue(*var);
    }
    for (auto const& var: localVariablesIncludingModifiers(*m_currentFunction, m_currentContract)) {
        m_context.changedValue(*var);
    }

    if (m_context.changedState()) {
        m_context.state().newState();
    }


    // can i generate invariants??
    std::cout << hasLoopOrRecursion << " " << hasLoopOrRecursionPrev << " " << hasBranch << " " << hasBranchPrev << " " << firstPass << "\n";
    bool canGenInvariants = ! ((hasLoopOrRecursionPrev > 0) || (hasLoopOrRecursion > hasLoopOrRecursionPrev + 1) || (hasBranch > hasBranchPrev) || (firstPass));
    m_invariant_checker.setEncoder(this);
    if (source_invariants_generated && m_invariant_checker.check_saved_invariants(&_while)) {
        std::cout << "Invariants added to encoding\n";
        // invariants already generated
        // convert invariants to expressions 
        // connect saved precondition block to loop header block with invariant as condition
        auto invariant = m_invariant_checker.get_saved_invariants(&_while);
        connectBlocks(m_currentBlock, predicate(*loopHeaderBlock), invariant);

    }
    else if (canGenInvariants && !source_invariants_generated) {
        std::cout << "Invariants generated\n";
        // if yes...
        // generate candidates
        std::vector<Invariant> initial_candidates, inductive_candidates, invariants;
        CandidateStore candidate_invariants;
        candidate_invariants.function = m_currentFunction;
        candidate_invariants.contract = m_currentContract;
        candidate_invariants.loop = &_while;
        candidate_invariants.header = loopHeaderBlock;
        candidate_invariants.precondition = preconditionTestBlock;
        candidate_invariants.candidates.clear();
        candidate_invariants.changed_vars = m_context.m_changed_variables;
        candidate_invariants.changed_state = m_context.m_changed_state;
// generate candidates
        m_invariant_checker.generateCandidates(candidate_invariants.candidates, candidate_invariants.changed_vars);
// generate targets
        m_invariant_checker.generatePreconditionTargets(*preconditionTestBlock, candidate_invariants.candidates, candidate_invariants.precondition_targets);
        m_invariant_checker.generateInductiveTargets(*inductiveTestBlock, candidate_invariants.candidates, candidate_invariants.inductive_targets);
        // check precon using precon block
        // m_invariant_checker.testPrecondition(*preconditionTestBlock, initial_candidates, inductive_candidates);
        // check inductive using loop header and inductive test block
        // m_invariant_checker.testInductive(preconditionPredicate ,*loopHeaderBlock, *inductiveTestBlock, inductive_candidates, invariants);
        // connect old precondition block with loop header wiht invariant as precondition
        // not necessary as these rules are already bad and wont be used to prove anything in the future
        // connectBlocks(m_currentBlock, preconditionTestBlock, )
        InvariantTargets.push_back(candidate_invariants);
        // m_invariant_checker.save_invariants(invariants, &_while);
    }
    else {
        if (firstPass) std::cout << "First pass\n"; 
        else std::cout << "Invariants not generated\n";
        // if no..
        // push scope etc if required idt this is required
        // connect inductive test to loop header
        setCurrentBlock(*inductiveTestBlock);
        connectBlocks(m_currentBlock, predicate(*loopHeaderBlock));
        // connect precon + to loop header
        setCurrentBlock(*preconditionTestBlock);
        connectBlocks(m_currentBlock, predicate(*loopHeaderBlock));
    }

	setCurrentBlock(*afterLoopBlock); 

	if (m_unknownFunctionCallSeen)
		eraseKnowledge();

	m_unknownFunctionCallSeen = unknownFunctionCallWasSeen;

	return false;
}

bool CHCInv::visitFor(ForStatement const& _for) {
    int hasLoopOrRecursionPrev = hasLoopOrRecursion;
    hasLoopOrRecursion += 1;
    int hasBranchPrev = hasBranch;


	m_scopes.push_back(&_for);

	bool unknownFunctionCallWasSeen = m_unknownFunctionCallSeen;
	m_unknownFunctionCallSeen = false;

	solAssert(m_currentFunction, "");
	auto const& functionBody = m_currentFunction->body();

	auto loopHeaderBlock = createBlock(&_for, PredicateType::FunctionBlock, "for_header_");
    // declare precondition test block
    auto preconditionTestBlock = createBlock(&_for, PredicateType::FunctionBlock,  "for_precondition_test_");
	auto loopBodyBlock = createBlock(&_for.body(), PredicateType::FunctionBlock, "for_body_");
    // declare inductive test block
    auto inductiveTestBlock = createBlock(&_for, PredicateType::FunctionBlock, "for_inductive_test_");
	auto afterLoopBlock = createBlock(&functionBody, PredicateType::FunctionBlock);
	auto postLoop = _for.loopExpression();
	auto postLoopBlock = postLoop ? createBlock(postLoop, PredicateType::FunctionBlock, "for_post_") : nullptr;

	auto outerBreakDest = m_breakDest;
	auto outerContinueDest = m_continueDest;
	m_breakDest = afterLoopBlock;
	m_continueDest = postLoop ? postLoopBlock : loopHeaderBlock;

	if (auto init = _for.initializationExpression())
		init->accept(*this);

    // connect to precondition test
    connectBlocks(m_currentBlock, predicate(*preconditionTestBlock));
	// connectBlocks(m_currentBlock, predicate(*loopHeaderBlock));
	setCurrentBlock(*loopHeaderBlock);
    m_context.resetChangedVariables();
	auto condition = smtutil::Expression(true);

    m_invariant_checker.resetConstants();
    saveConstants = true;
	if (auto forCondition = _for.condition())
	{
		forCondition->accept(*this);
		condition = expr(*forCondition);
	}
    saveConstants = false;

	connectBlocks(m_currentBlock, predicate(*loopBodyBlock), condition);
	connectBlocks(m_currentBlock, predicate(*afterLoopBlock), !condition);

	// Loop body visit.
	setCurrentBlock(*loopBodyBlock);
	_for.body().accept(*this);

	if (postLoop)
	{
		connectBlocks(m_currentBlock, predicate(*postLoopBlock));
		setCurrentBlock(*postLoopBlock);
		postLoop->accept(*this);
	}

	m_breakDest = outerBreakDest;
	m_continueDest = outerContinueDest;

    connectBlocks(m_currentBlock, predicate(*inductiveTestBlock));

	// Back edge.
	// connectBlocks(m_currentBlock, predicate(*loopHeaderBlock));

    setCurrentBlock(*preconditionTestBlock);
    auto preconditionPredicate = predicate(*preconditionTestBlock);

    for (auto const* var: m_stateVariables) {
        m_context.changedValue(*var);        
    }
    for (auto const& var: m_currentFunction->parameters() + m_currentFunction->returnParameters()) {
        m_context.changedValue(*var);
    }
    for (auto const& var: localVariablesIncludingModifiers(*m_currentFunction, m_currentContract)) {
        m_context.changedValue(*var);
    }
    
    if (m_context.changedState()) {
        m_context.state().newState();
    }

    // can i generate invariants??
    bool canGenInvariants = ! ((hasLoopOrRecursionPrev > 0) || (hasLoopOrRecursion > hasLoopOrRecursionPrev + 1) || (hasBranch > hasBranchPrev) || (firstPass));
    m_invariant_checker.setEncoder(this);
    if (source_invariants_generated && m_invariant_checker.check_saved_invariants(&_for)) {
        std::cout << "Invariants added to encoding\n";
        // invariants already generated
        // convert invariants to expressions 
        // connect saved precondition block to loop header block with invariant as condition
        auto invariant = m_invariant_checker.get_saved_invariants(&_for);
        connectBlocks(m_currentBlock, predicate(*loopHeaderBlock), invariant);

    }
    else if (canGenInvariants && !source_invariants_generated) {
        std::cout << "Invariants generated\n";
        // if yes...
        // generate candidates
        std::vector<Invariant> initial_candidates, inductive_candidates, invariants;
        CandidateStore candidate_invariants;
        candidate_invariants.function = m_currentFunction;
        candidate_invariants.contract = m_currentContract;
        candidate_invariants.loop = &_for;
        candidate_invariants.header = loopHeaderBlock;
        candidate_invariants.precondition = preconditionTestBlock;
        candidate_invariants.candidates.clear();
        candidate_invariants.changed_vars = m_context.m_changed_variables;
        candidate_invariants.changed_state = m_context.m_changed_state;
// generate candidates
        m_invariant_checker.generateCandidates(candidate_invariants.candidates, candidate_invariants.changed_vars);
// generate targets
        m_invariant_checker.generatePreconditionTargets(*preconditionTestBlock, candidate_invariants.candidates, candidate_invariants.precondition_targets);
        m_invariant_checker.generateInductiveTargets(*inductiveTestBlock, candidate_invariants.candidates, candidate_invariants.inductive_targets);
        // check precon using precon block
        // m_invariant_checker.testPrecondition(*preconditionTestBlock, initial_candidates, inductive_candidates);
        // check inductive using loop header and inductive test block
        // m_invariant_checker.testInductive(preconditionPredicate ,*loopHeaderBlock, *inductiveTestBlock, inductive_candidates, invariants);
        // connect old precondition block with loop header wiht invariant as precondition
        // not necessary as these rules are already bad and wont be used to prove anything in the future
        // connectBlocks(m_currentBlock, preconditionTestBlock, )
        InvariantTargets.push_back(candidate_invariants);
        // m_invariant_checker.save_invariants(invariants, &_while);
    }
    else {
        std::cout << "Invariants not generated\n";
        // if no..
        // push scope etc if required idt this is required
        // connect inductive test to loop header
        setCurrentBlock(*inductiveTestBlock);
        connectBlocks(m_currentBlock, predicate(*loopHeaderBlock));
        // connect precon + to loop header
        setCurrentBlock(*preconditionTestBlock);
        connectBlocks(m_currentBlock, predicate(*loopHeaderBlock));
    }

	setCurrentBlock(*afterLoopBlock); 

	if (m_unknownFunctionCallSeen)
		eraseKnowledge();

	m_unknownFunctionCallSeen = unknownFunctionCallWasSeen;

	return false;
}



bool CHCInv::visit(WhileStatement const& _while) {
    if (_while.isDoWhile()) {
        return CHC::visit(_while);
    }
    else {
        return visitWhile(_while);
    }
}

bool CHCInv::visit(ForStatement const& _for){
    return visitFor(_for);
}

smtutil::Expression CHCInv::invariant()
{
	return (*m_InvariantPredicate)({});
}

void CHCInv::endVisit(Literal const& _literal) {
    Type const& type = *_literal.annotation().type;
    if (smt::isNumber(type)) {
        auto literalValue = smtutil::Expression(type.literalValue(&_literal));
        if (saveConstants) {
            m_invariant_checker.addConstant(literalValue);
        }
    }
    CHC::endVisit(_literal);
    return;
}



// InvariantHandler 

void InvariantHandler::setEncoder(CHCInv* _encoder) {
    m_encoder = _encoder;
    return;
}

void InvariantHandler::addConstant(smtutil::Expression _constant) {
    m_constants.push_back(_constant);
    return;
}

void InvariantHandler::resetConstants() {
    m_constants.clear();
    m_constants.push_back(smtutil::Expression((size_t) 0));
    m_constants.push_back(smtutil::Expression((size_t) 1));
    return;
}

void InvariantHandler::generateCandidates(std::vector<Invariant> &_candidates, std::set<const VariableDeclaration*> &changed_vars) {
    std::vector<const VariableDeclaration*> int_vars;
    std::vector<const VariableDeclaration*> bool_vars;
    std::vector<const VariableDeclaration*> array_vars;
    
    for (auto const* var : m_encoder->m_stateVariables) {
        auto _type = var->type();
        if (isInteger(*_type)) {
            int_vars.push_back(var);
        }
        if (isBool(*_type)) {
            bool_vars.push_back(var);
        }
        if (isArray(*_type) || isMapping(*_type)) {
            array_vars.push_back(var);
        }
    
    }
        
    for (auto const& var: m_encoder->m_currentFunction->parameters() + m_encoder->m_currentFunction->returnParameters()) {
        auto _type = var->type();
        if (isInteger(*_type)) {
            int_vars.push_back(var.get());
        }
        if (isBool(*_type)) {
            bool_vars.push_back(var.get());
        }
        if (isArray(*_type) || isMapping(*_type)) {
            array_vars.push_back(var.get());
        }
    }

    for (auto const& var: m_encoder->localVariablesIncludingModifiers(*m_encoder->m_currentFunction, m_encoder->m_currentContract)) {
        auto _type = var->type();
        if (isInteger(*_type)) {
            int_vars.push_back(var);
        }
        if (isBool(*_type)) {
            bool_vars.push_back(var);
        }
        if (isArray(*_type) || isMapping(*_type)) {
            array_vars.push_back(var);
        }
    }

    // int_constants.push_back(-1, 0, 1, 5, 10);
	
    for (size_t i = 0; i < int_vars.size(); i++) {
        for (size_t j = 0; j < int_vars.size(); j++) {
            if (changed_vars.find(int_vars[i]) == changed_vars.end()) continue;
            if (changed_vars.find(int_vars[j]) != changed_vars.end() && i <= j) continue;

            Invariant _candidate3(int_vars[i], RelOp::GE, int_vars[j]);
            _candidates.push_back(_candidate3);
            Invariant _candidate4(int_vars[i], RelOp::LE, int_vars[j]);
            _candidates.push_back(_candidate4);
            Invariant _candidate6(int_vars[i], RelOp::EQ, int_vars[j]);
            _candidates.push_back(_candidate4);
        }
    }

    for (size_t i = 0; i < int_vars.size(); i++) {
        for (auto _const: m_constants) {
            if (changed_vars.find(int_vars[i]) == changed_vars.end()) continue;
            // EQ, LT, GT, LE, GE
            Invariant _candidate1(int_vars[i], RelOp::EQ, _const, false);
            _candidates.push_back(_candidate1);
            Invariant _candidate3(int_vars[i], RelOp::GE, _const, false);
            _candidates.push_back(_candidate3);
            Invariant _candidate4(int_vars[i], RelOp::LE, _const, false);
            _candidates.push_back(_candidate4);
        }
    }

    // boolean vars
    for (size_t i = 0; i < bool_vars.size(); i++) {
        if (changed_vars.find(bool_vars[i]) == changed_vars.end()) continue;
        Invariant _candidate1(bool_vars[i], true);
        _candidates.push_back(_candidate1);
        Invariant _candidate4(bool_vars[i], false);
        _candidates.push_back(_candidate4);
    }

    for (size_t i = 0; i < array_vars.size(); i++) {
        for (auto _const: m_constants) {
            if (changed_vars.find(array_vars[i]) == changed_vars.end()) continue;
            // EQ, LT, GT, LE, GE
            Invariant _candidate1(array_vars[i], RelOp::EQ, _const, true);
            _candidates.push_back(_candidate1);
            Invariant _candidate3(array_vars[i], RelOp::GE, _const, true);
            _candidates.push_back(_candidate3);
            Invariant _candidate4(array_vars[i], RelOp::LE, _const, true);
            _candidates.push_back(_candidate4);
        }
    }

    return;
}

smtutil::Expression InvariantHandler::invariantToExpression(Invariant _inv) {
    if (_inv.isConst && !_inv.isBoolean) {
        return invariantToExpression(_inv.var1, _inv.relop, _inv.intConst, _inv.isArray);
    }
    else if (!_inv.isConst && !_inv.isBoolean) {
        return invariantToExpression(_inv.var1, _inv.relop, _inv.var2);
    }
    else if (_inv.isConst && _inv.isBoolean) {
        return invariantToExpression(_inv.var1, _inv.boolVal);
    }
    return smtutil::Expression(false);
}

smtutil::Expression InvariantHandler::invariantToExpression(const VariableDeclaration* var1, RelOp op, const VariableDeclaration* var2) {
    auto symVar1 = m_encoder->m_context.variable(*var1)->currentValue();
    auto symVar2 = m_encoder->m_context.variable(*var2)->currentValue();
 
    switch (op) {
        case RelOp::EQ :
            return symVar1 != symVar2;
        case RelOp::GE :
            return symVar1 >= symVar2;
        case RelOp::LE :
            return symVar1 <= symVar2;
        default:
            return smtutil::Expression(false);
    }
}

smtutil::Expression InvariantHandler::invariantToExpression(const VariableDeclaration* var1, RelOp op, smtutil::Expression intConst, bool isArray) {
    smtutil::Expression symVar1 = (isArray) ? std::dynamic_pointer_cast<smt::SymbolicArrayVariable>(m_encoder->m_context.variable(*var1))->length() 
                                            : m_encoder->m_context.variable(*var1)->currentValue(); 
    smtutil::Expression _intConst = intConst;
    switch (op) {
        case RelOp::EQ :
            return symVar1 != _intConst;
        case RelOp::GE :
            return symVar1 >= _intConst;
        case RelOp::LE :
            return symVar1 <= _intConst;
        default:
            return smtutil::Expression(false);
    }
}

smtutil::Expression InvariantHandler::invariantToExpression(const VariableDeclaration* var1, bool boolValue) {
    auto symVar1 = m_encoder->m_context.variable(*var1)->currentValue();
    // (void) boolValue;
    // std::cout << symVar1.name << std::endl;
    // return symVar1;
    return symVar1 == smtutil::Expression(boolValue);
}

void InvariantHandler::generatePreconditionTargets(const Predicate& _precondition_block, std::vector<Invariant> &candidates, std::vector<const Predicate *> &targets) {
    for (auto _candidate: candidates) {
        m_encoder->createInvariantCheckerBlock();
        // connect current block with error target + not invariant
        m_encoder->connectBlocks(m_encoder->predicate(_precondition_block) , m_encoder->invariant(), !invariantToExpression(_candidate));
        targets.push_back(m_encoder->m_InvariantPredicate);
    }
    return;
}

void InvariantHandler::generateInductiveTargets(const Predicate& _inductive_block, std::vector<Invariant> &candidates, std::vector<const Predicate *> &targets) {
    for (auto _candidate: candidates) {
        m_encoder->createInvariantCheckerBlock();
        // connect current block with error target + not invariant
        m_encoder->connectBlocks(m_encoder->predicate(_inductive_block) , m_encoder->invariant(), !invariantToExpression(_candidate));
        targets.push_back(m_encoder->m_InvariantPredicate);
    }
    return;
}

void InvariantHandler::testPrecondition(const Predicate& _precondition_block, std::vector<Invariant> &candidates, std::vector<Invariant> &proved) {
    for (auto _candidate: candidates) {
        m_encoder->createInvariantCheckerBlock();
        // connect current block with error target + not invariant
        m_encoder->connectBlocks(m_encoder->predicate(_precondition_block) , m_encoder->invariant(), !invariantToExpression(_candidate));
        auto query = m_encoder->invariant();
        // query solver interface
        auto result = (m_encoder->m_interface)->query(query);
        // push_back verified invariants
        switch (result.answer) 
        {
            case (CheckResult::SATISFIABLE):
            {
                std::cout << "SAT: Not an invariant\n";
                break;
            }
            case (CheckResult::UNSATISFIABLE):
            {
                std::cout << "UNSAT: Is an invariant\n";
                proved.push_back(_candidate);
                break;
            }
            default:
            {
                std::cout << "Default case \n";
            }
        }
    }
    return;
}


void InvariantHandler::testPreconditionNew(std::vector<Invariant> &candidates, std::vector<const Predicate*> &targetsPre, std::vector<const Predicate*> &targetsInd) {
    std::vector<Invariant> proved;
    std::vector<const Predicate*> proved_targets_inductive;
    for (long unsigned int i = 0; i < candidates.size(); i++) {
        auto query = m_encoder->predicate(*targetsPre[i]);
        auto result = (m_encoder->m_interface)->query(query);
        switch (result.answer) 
        {
            case (CheckResult::SATISFIABLE):
            {
                std::cout << "SAT: Not an invariant\n";
                break;
            }
            case (CheckResult::UNSATISFIABLE):
            {
                std::cout << "UNSAT: Is an invariant\n";
                proved.push_back(candidates[i]);
                proved_targets_inductive.push_back(targetsInd[i]);
                break;
            }
            default:
            {
                std::cout << "Default case \n";
            }
        }
    }

    targetsInd = proved_targets_inductive;
    candidates = proved;
    return;
}


void InvariantHandler::testInductiveNew(smtutil::Expression& _precondition_block, const Predicate& _header_block, std::vector<Invariant> &candidates, std::vector<const Predicate*> &targetsInd)  {
    // current block should be inductive block
    std::vector<Invariant> cur_candidates;
    std::vector<const Predicate*> cur_targets;


    while (cur_candidates.size() != candidates.size()) {
        std::cout << "Inductive test loop itr\n";
        cur_candidates = candidates;
        cur_targets = targetsInd;
        candidates.clear();
        targetsInd.clear();

        smtutil::Expression conjunction = smtutil::Expression(true);
        for (auto _candidate: cur_candidates) {
            conjunction = conjunction && invariantToExpression(_candidate);
        }
        // connect precondition to header
        m_encoder->connectBlocks(_precondition_block, m_encoder->predicate(_header_block), conjunction);
        long unsigned int i = 0;
        for (auto _candidate: cur_candidates) {
            auto query = m_encoder->predicate(*cur_targets[i]);
            // query solver interface
            auto result = (m_encoder->m_interface)->query(query);
            // push_back verified invariants
            switch (result.answer) 
            {
                case (CheckResult::SATISFIABLE):
                {
                    std::cout << "SAT: Not an invariant\n";
                    break;
                }
                case (CheckResult::UNSATISFIABLE):
                {
                    std::cout << "UNSAT: Is an invariant\n";
                    targetsInd.push_back(cur_targets[i]);
                    candidates.push_back(_candidate);
                    break;
                }
                default:
                {
                    std::cout << "Default case \n";
                }
            }
            i++;
        }

    }

    return;
}

void InvariantHandler::testInductive(smtutil::Expression& _precondition_block, const Predicate& _header_block, const Predicate& _inductive_block, std::vector<Invariant> &candidates, std::vector<Invariant> &proved)  {
    // current block should be inductive block
    std::vector<Invariant> cur_candidates;
    std::vector<smtutil::Expression> cur_targets, targets;
    proved.clear();

    for (auto _candidate: candidates) {
        m_encoder->createInvariantCheckerBlock();
        // connect inductive block with error target + not invariant
        m_encoder->connectBlocks(m_encoder->predicate(_inductive_block), m_encoder->invariant(), !invariantToExpression(_candidate));
        targets.push_back(m_encoder->invariant());
    }

    while (cur_candidates.size() != candidates.size()) {
        std::cout << "Inductive test loop itr\n";
        cur_candidates = candidates;
        cur_targets = targets;
        candidates.clear();
        targets.clear();

        smtutil::Expression conjunction = smtutil::Expression(true);
        for (auto _candidate: cur_candidates) {
            conjunction = conjunction && invariantToExpression(_candidate);
        }
        // connect precondition to header
        m_encoder->connectBlocks(_precondition_block, m_encoder->predicate(_header_block), conjunction);
        long unsigned int i = 0;
        for (auto _candidate: cur_candidates) {
            auto query = cur_targets[i];
            // query solver interface
            auto result = (m_encoder->m_interface)->query(query);
            // push_back verified invariants
            switch (result.answer) 
            {
                case (CheckResult::SATISFIABLE):
                {
                    std::cout << "SAT: Not an invariant\n";
                    break;
                }
                case (CheckResult::UNSATISFIABLE):
                {
                    std::cout << "UNSAT: Is an invariant\n";
                    targets.push_back(cur_targets[i]);
                    candidates.push_back(_candidate);
                    break;
                }
                default:
                {
                    std::cout << "Default case \n";
                }
            }
            i++;
        }

    }

    proved = candidates;
    (void) _inductive_block;
    return;
}

void InvariantHandler::save_invariants(std::vector<Invariant> &_invariants, const Statement* loop) {
    m_saved_invariants[loop] = _invariants;
}

smtutil::Expression InvariantHandler::get_saved_invariants(const Statement* loop) {
    solAssert(m_saved_invariants.find(loop) != m_saved_invariants.end());

    smtutil::Expression conjunction = smtutil::Expression(true);
    for (auto _invar: m_saved_invariants[loop]) {
        conjunction = conjunction && invariantToExpression(_invar);
    }

    return conjunction;
}

bool InvariantHandler::check_saved_invariants(const Statement* loop){
    return m_saved_invariants.find(loop) != m_saved_invariants.end();
}