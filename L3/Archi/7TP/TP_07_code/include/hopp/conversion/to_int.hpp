// Copyright © 2012, 2014, 2015 Lénaïc Bagnères, hnc@singularity.fr

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


#ifndef HOPP_CONVERSATION_TO_INT_HPP
#define HOPP_CONVERSATION_TO_INT_HPP

#include "to_type.hpp"


namespace hopp
{
	/**
	 * @brief Get a int from an input (using hopp:to_)
	 *
	 * @code
	   #include <hopp/conversion.hpp>
	   @endcode
	 *
	 * @param[in] in Input
	 *
	 * @return the int from the input
	 *
	 * @ingroup hopp_conversion
	 */
	template <class T>
	int to_int(T const & in) { return hopp::to_<int>(in); }
}

#endif
