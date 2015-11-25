// Copyright © 2014, 2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_ALGO_TO_UPPER_HPP
#define HOPP_ALGO_TO_UPPER_HPP

#include <locale>


namespace hopp
{
	namespace algo
	{
		/**
		 * @brief Convert all letters to uppercase
		 *
		 * @code
		   #include <hopp/algo.hpp>
		   @endcode
		 *
		 * @param[in] first Forward iterator to the initial position
		 * @param[in] last  Forward iterator to the final position (not included)
		 *
		 * @ingroup hopp_algo
		 */
		template <class forward_iterator_t>
		void to_upper
		(
			forward_iterator_t const & first,
			forward_iterator_t const & last
		)
		{
			using char_t = typename forward_iterator_t::value_type;
			
			for (forward_iterator_t it = first; it != last; ++it)
			{
				*it = char_t(std::toupper(*it));
			}
		}
		
		/**
		 * @brief Convert all letters to uppercase
		 *
		 * @code
		   #include <hopp/algo.hpp>
		   @endcode
		 *
		 * @param[in] c Container of char (like std::string, std::vector<char>)
		 *
		 * @ingroup hopp_algo
		 */
		template <class container>
		void to_upper(container & c)
		{
			hopp::algo::to_upper(c.begin(), c.end());
		}
		
		/**
		 * @brief Convert all letters to uppercase in a new container
		 *
		 * @code
		   #include <hopp/algo.hpp>
		   @endcode
		 *
		 * @param[in] c Container of char (like std::string, std::vector<char>)
		 *
		 * @return a new container with uppercase letters
		 *
		 * @ingroup hopp_algo
		 */
		template <class container>
		container to_upper_copy(container const & c)
		{
			container copy(c);
			hopp::algo::to_upper(copy);
			return copy;
		}
	}
}

#endif
