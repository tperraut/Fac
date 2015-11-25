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


#ifndef HOPP_ALGO_RANDOM_ELEMENT_HPP
#define HOPP_ALGO_RANDOM_ELEMENT_HPP

#include <iterator>

#include "../random.hpp"


namespace hopp
{
	/// @brief Return a random element from a range
	/// @param[in] first Iterator to the first element
	/// @param[in] last  Iterator to the last element (not included)
	/// @return a random element
	/// @ingroup hopp_algo
	template <class forward_iterator_t>
	auto random_element(forward_iterator_t const & first, forward_iterator_t const & last) -> decltype(*first) &
	{
		using diff_t = typename std::iterator_traits<forward_iterator_t>::difference_type;
		
		return *std::next(first, hopp::random::uniform(diff_t(0), diff_t(std::distance(first, last) - 1)));
	}
	
	/// @brief Return a copy of a random element from a range
	/// @param[in] first Iterator to the first element
	/// @param[in] last  Iterator to the last element (not included)
	/// @return a copy of a random element
	/// @ingroup hopp_algo
	template <class forward_iterator_t>
	auto random_element_copy(forward_iterator_t const & first, forward_iterator_t const & last) -> typename std::decay<decltype(*first)>::type
	{
		return hopp::random_element(first, last);
	}
	
	/// @brief Return a random element from a container
	/// @param[in] c A container
	/// @return a random element
	/// @ingroup hopp_algo
	template <class container_t>
	auto random_element(container_t & c) -> decltype(*std::begin(c)) &
	{
		return hopp::random_element(std::begin(c), std::end(c));
	}
	
	/// @brief Return a random element from a container
	/// @param[in] c A container
	/// @return a random element
	/// @ingroup hopp_algo
	template <class container_t>
	auto random_element(container_t const & c) -> decltype(*std::begin(c)) const &
	{
		return hopp::random_element(std::begin(c), std::end(c));
	}
	
	/// @brief Return a copy of a random element from a container
	/// @param[in] c A container
	/// @return  a copy of a random element
	/// @ingroup hopp_algo
	template <class container_t>
	auto random_element_copy(container_t const & c) -> typename std::decay<decltype(*std::begin(c))>::type
	{
		return hopp::random_element_copy(std::begin(c), std::end(c));
	}
}

#endif
