
#include <libsolidity/formal/DependencyHandler.h>


//todo: array push or any other modifications which arent assignments

namespace solidity::frontend
{

void DependencyHandler::reset() {
    m_current_contract = nullptr;
    active = false;
    contract_funcs.clear();
    out_edges.clear();
    summary_clause.clear();
	modified_vars.clear();
	used_vars.clear();
    uses_balance.clear();
    has_branch.clear();
    has_loop_or_recursion.clear(); 
}

void DependencyHandler::activate() {
    active = true;
    return;
}

void DependencyHandler::deactivate() {
    active = false;
    return;
}

bool DependencyHandler::functionHasBranch(const FunctionDefinition* function) {
    if (active) {
        return false;
    }
    return has_branch[function];
}

bool DependencyHandler::functionHasLoopOrRecursion(const FunctionDefinition* function) {
    if (active) {
        return false;
    }
    return has_loop_or_recursion[function];
}

void DependencyHandler::setFunctionHasBranch(const FunctionDefinition* function) {
    if (!active) {
        return;
    }
    has_branch[function] = true;
    return ;
}

void DependencyHandler::setFunctionHasLoopOrRecursion(const FunctionDefinition* function) {
    if (!active) {
        return ;
    }
    has_loop_or_recursion[function] = true;
    return;
}

void DependencyHandler::setCurrentContract(const ContractDefinition* contract) {
    if (!active) {
        return;
    }
    m_current_contract = contract;
    contract_funcs[m_current_contract] = std::set<const FunctionDefinition*, frontend::ASTCompareByID<ASTNode>>();
    return;
}

void DependencyHandler::mapFunctionSummary(const FunctionDefinition* func_def, const ContractDefinition* contract_def, std::string summary_name) {
    if (!active) {
        return;
    }
    summary_clause[contract_def][func_def] = summary_name;
    return;
}

void DependencyHandler::addFunctionToCurrentContract(const FunctionDefinition* func_def) {
    if (!active) {
        return;
    }
    if (out_edges.find(func_def) == out_edges.end()) {
        out_edges[func_def] =  std::set<const FunctionDefinition*, frontend::ASTCompareByID<ASTNode>> ();
        modified_vars[func_def] = std::set<const VariableDeclaration*, frontend::ASTCompareByID<ASTNode>> ();
        used_vars[func_def] = std::set<const VariableDeclaration*, frontend::ASTCompareByID<ASTNode>> ();
        uses_balance[func_def] = false;
        has_loop_or_recursion[func_def] = false;
        has_branch[func_def] = false;
    }
    if (summary_clause[m_current_contract].find(func_def) != summary_clause[m_current_contract].end()) {
        contract_funcs[m_current_contract].insert(func_def);
    }
    return;
}
void DependencyHandler::addEdge(const FunctionDefinition* func_def_1, const FunctionDefinition* func_def_2) {
    if (!active) {
        return;
    }
    out_edges[func_def_1].insert(func_def_2);
    return;
}
void DependencyHandler::addVariableAssignment(const VariableDeclaration* var_decl, const FunctionDefinition* func_def) {
    if (!active) {
        return;
    }
    // std::cout << "assignment" << var_decl->name() << " " << func_def->name() << std::endl;
    modified_vars[func_def].insert(var_decl);
    return;
}
void DependencyHandler::addVariableUse(const VariableDeclaration* var_decl, const FunctionDefinition* func_def) {
    if (!active) {
        return;
    }
    // std::cout << "use" << var_decl->name() << " " << func_def->name() << std::endl;
    used_vars[func_def].insert(var_decl);
    return;
}

void DependencyHandler::addBalanceUse(const FunctionDefinition* func_def) {
    if (!active) {
        return;
    }
    std::cout <<  "balance used: " << func_def->name() << std::endl;
    uses_balance[func_def] = true;
    return;
}


void DependencyHandler::dependancyUpdateOne(const FunctionDefinition * _func){
    if (out_edges[_func].find(_func) != out_edges[_func].end()) {
        has_loop_or_recursion[_func] = true;
    }

	for (auto _callee: out_edges[_func]){
        // std::cout << "callees exist";
		for (auto _used_var: used_vars[_callee]) {
			used_vars[_func].insert(_used_var);
		}
		for (auto _mod_var: modified_vars[_callee]) {
			modified_vars[_func].insert(_mod_var);
		}
        uses_balance[_func] = uses_balance[_callee] || uses_balance[_func];

        if (has_loop_or_recursion[_callee]) {
            has_loop_or_recursion[_func] = true;
        }
        if (has_branch[_callee]) {
            has_branch[_func] = true;
        }

	}
	return;
}


void DependencyHandler::dependancyUpdateAll(){
	for (auto _pair: out_edges) {
		dependancyUpdateOne(_pair.first);
	}
	return;
}

bool DependencyHandler::checkEdge(const FunctionDefinition * _src, const FunctionDefinition * _dst) {
	auto _dst_used_vars = used_vars[_dst];
	for (auto _src_mod : modified_vars[_src]) {
		if (_dst_used_vars.find(_src_mod) == _dst_used_vars.end()) {
			continue;
		}
		else {
			return true;
		}
	}
	return uses_balance[_dst];
}

std::map<std::string, std::set<std::string>> DependencyHandler::getDependancyGraph(const ContractDefinition* contract) {
	std::map<std::string, std::set<std::string>> dependancyGraph;

    auto funcs = contract_funcs[contract];

	for (auto _caller: funcs) {
		std::string _caller_name = summary_clause[contract][_caller];
		dependancyGraph[_caller_name] = std::set<std::string> ();
		for (auto _callee: funcs) {
			std::string _callee_name = summary_clause[contract][_callee];
			if (checkEdge(_caller, _callee)) {
				dependancyGraph[_caller_name].insert(_callee_name);
			}
		}
	}

	return dependancyGraph;
}

void DependencyHandler::printDependancyGraph() {
    std::cout << "Graph printer called \n";
    if (!active) {
        return;
    }
    std::cout << "Graph printer active \n";
	auto _sz = out_edges.size();
	while (_sz--) {
		dependancyUpdateAll();
	}

    for (auto contract_func_itr: contract_funcs) {
        auto contract = contract_func_itr.first;
        std::map<std::string, std::set<std::string>> dependancyGraph;
        dependancyGraph = getDependancyGraph(contract);
        std::cout << "(DEPENDANCY-GRAPH-DELIMITER)\n";
        if (contract) {
            std::cout << "(CONTRACT-NAME-DELIMTER)" << contract->name() << "(CONTRACT-NAME-DELIMTER)\n"; 
        }
        
        std::cout << dependancyGraph.size() << std::endl;
        for (auto _pair: dependancyGraph) {
            std::cout << _pair.first << " " << _pair.second.size() << std::endl;
            for (auto _dst: _pair.second) {
                std::cout << _dst << " ";
            }
            std::cout << std::endl;
        }
        std::cout << "(DEPENDANCY-GRAPH-DELIMITER)\n";

    }

}


void DependencyHandler::processFirstPass() {
    std::cout << "processing first pass \n";
    if (!active) {
        std::cout << "unexpected first pass not active\n";
        return;
    }
	auto _sz = out_edges.size() + 1;
	while (_sz--) {
		dependancyUpdateAll();
	}
    // graph should be complete now
    return;
}


}