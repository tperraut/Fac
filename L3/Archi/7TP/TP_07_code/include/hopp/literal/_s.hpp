// Copyright © 2013-2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_LITERAL_S_HPP
#define HOPP_LITERAL_S_HPP

#include <string>


/**
 * @brief std::string literal
 *
 * @code
   "A std::string, not a char []"_s // A std::string, not a zero-terminated array of characters
   @endcode
 *
 * http://www.stroustrup.com/C++11FAQ.html#UD-literals
 *
 * @ingroup hopp_literal
 */
std::string operator"" _s(char const * p, size_t const size)
{
	return std::string(p, size);
}

#endif
