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


#ifndef HOPP_ALGO_SUM_HPP
#define HOPP_ALGO_SUM_HPP

#include <iterator>
#include <type_traits>


namespace hopp
{
	/// @brief Sum of elements between two iterators
	/// @param[in] first Iterator to the first element
	/// @param[in] last  Iterator to the last element (not included)
	/// @return the sum
	/// @note Consider std::accumulate
	/// @ingroup hopp_algo
	template <class forward_iterator_t>
	auto sum(forward_iterator_t const & first, forward_iterator_t const & last) -> typename std::decay<decltype(*first)>::type
	{
		using sum_t = typename std::decay<decltype(*first)>::type; // typename std::iterator_traits<forward_iterator_t>::value_type;
		sum_t sum = sum_t();
		for (auto it = first; it != last; ++it) { sum += *it; }
		return sum;
	}
	
	/// @brief Sum of elements of a container
	///  @param[in] c Container like std::vector, std::list
	/// @return the sum
	/// @note Consider std::accumulate
	/// @ingroup hopp_algo
	template <class container_t>
	auto sum(container_t const & container) -> decltype(hopp::sum(std::begin(container), std::end(container)))
	{ return hopp::sum(std::begin(container), std::end(container)); }
}

#endif
