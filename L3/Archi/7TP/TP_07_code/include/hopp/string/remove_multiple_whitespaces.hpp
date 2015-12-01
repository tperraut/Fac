// Copyright © 2013, 2014 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_STRING_REMOVE_MULTIPLE_WHITESPACES_HPP
#define HOPP_STRING_REMOVE_MULTIPLE_WHITESPACES_HPP

#include <cctype>
#include <iterator>


namespace hopp
{
	/**
	 * @brief Replace multiple consecutive white-spaces by one space
	 *
	 * @code
	   #include <hopp/string.hpp>
	   @endcode
	 *
	 * @param[in] string A string
	 */
	template <class string_t>
	void remove_multiple_whitespaces(string_t & string)
	{
		auto it = std::begin(string);
		
		while (std::next(it) != std::end(string))
		{
			auto const next = std::next(it);
			
			if (std::isspace(int(*it)) && std::isspace(int(*next)))
			{
				*next = ' ';
				it = string.erase(it);
			}
			else
			{
				++it;
			}
		}
	}
	
	/**
	 * @brief Replace multiple consecutive white-spaces by one space
	 *
	 * @code
	   #include <hopp/string.hpp>
	   @endcode
	 *
	 * @param[in] string A string
	 *
	 * @return string without multiple white-spaces
	 */
	template <class string_t>
	string_t remove_multiple_whitespaces_copy(string_t const & string)
	{
		std::string copy = string;
		hopp::remove_multiple_whitespaces(copy);
		return copy;
	}
}

#endif
