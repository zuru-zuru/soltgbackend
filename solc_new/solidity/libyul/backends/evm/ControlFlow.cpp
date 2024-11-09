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

#include <libyul/backends/evm/ControlFlow.h>
#include <range/v3/range/conversion.hpp>

using namespace solidity::yul;

ControlFlowLiveness::ControlFlowLiveness(ControlFlow const& _controlFlow):
	controlFlow(_controlFlow),
	mainLiveness(std::make_unique<SSACFGLiveness>(*_controlFlow.mainGraph)),
	functionLiveness(_controlFlow.functionGraphs | ranges::views::transform([](auto const& _cfg) { return std::make_unique<SSACFGLiveness>(*_cfg); }) | ranges::to<std::vector>)
{ }
