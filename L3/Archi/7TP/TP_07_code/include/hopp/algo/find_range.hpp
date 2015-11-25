// Copyright © 2013-2015 Lénaïc Bagnères, hnc@singularity.fr

// This file is part of hopp.

// hopp is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// hopp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with hopp. If not, see <http://www.gnu.org/licenses/>


#ifndef HOPP_ALGO_FIND_RANGE_HPP
#define HOPP_ALGO_FIND_RANGE_HPP

#include <algorithm>

#include "compare_range.hpp"


namespace hopp
{
	/// @brief Find a sequence in an other sequence
	/// @param[in] first        Iterator to the first element
	/// @param[in] last         Iterator to the last element (not included)
	/// @param[in] values_first Iterator to the first element of the values that we are looking for
	/// @param[in] values_last  Iterator to the last element (upper bound) of the values that we are looking for (not included)
	/// @return a iterator to the the first element of the finded sequence, last if not found
	/// @note Consider Boost.Range
	/// @note Consider std::find to find one element in a sequence
	/// @ingroup hopp_algo
	template <class forward_iterator_t0, class forward_iterator_t1>
	forward_iterator_t0 find_range
	(
		forward_iterator_t0 first, forward_iterator_t0 const & last,
		forward_iterator_t1 const & values_first, forward_iterator_t1 const & values_last
	)
	{
		typename std::iterator_traits<forward_iterator_t1>::difference_type values_size = std::distance(values_first, values_last);
		
		if (values_size != 0)
		{
			// Find the first element of values
			forward_iterator_t0 it = std::find(first, last, *values_first);
			
			// it to last can not contains the values
			while (it != last && std::distance(it, last) >= values_size)
			{
				// Compare this position with values
				bool ranges_are_equal = hopp::compare_range(it, std::next(it, values_size), values_first, values_last);
				
				// Range found
				if (ranges_are_equal)
				{
					return it;
				}
				
				++it;
				it = std::find(it, last, *values_first);
			}
		}
		
		return last;
	}
	
	/// @brief Find a sequence (a container) in an other sequence
	/// @param[in] first  Iterator to the first element
	/// @param[in] last   Iterator to the last element (not included)
	/// @param[in] values Values we are looking for
	/// @return a iterator to the the first element of the finded sequence, last if not found
	/// @note Consider Boost.Range
	/// @note Consider std::find to find one element in a sequence
	/// @ingroup hopp_algo
	template <class forward_iterator_t, class container_t>
	forward_iterator_t find_range
	(
		forward_iterator_t first, forward_iterator_t const & last,
		container_t const & values
	)
	{
		return hopp::find_range(first, last, std::begin(values), std::end(values));
	}
	
	/// @brief Find a container in an other const container
	/// @param[in] c      A container
	/// @param[in] values Values we are looking for
	/// @return a const iterator on the first element of the finded sequence, last if not found
	/// @note Consider std::find to find one element in a sequence
	/// @ingroup hopp_algo
	template <class container_t>
	typename container_t::const_iterator find_range
	(
		container_t const & c,
		container_t const & values
	)
	{
		return hopp::find_range(std::begin(c), std::end(c), std::begin(values), std::end(values));
	}
	
	/// @brief Find a container in an other container
	/// @param[in] c      A container
	/// @param[in] values Values we are looking for
	/// @return a iterator on the first element of the finded sequence, last if not found
	/// @note Consider std::find to find one element in a sequence
	/// @ingroup hopp_algo
	template <class container_t>
	typename container_t::iterator find_range
	(
		container_t & c,
		container_t const & values
	)
	{
		return hopp::find_range(std::begin(c), std::end(c), std::begin(values), std::end(values));
	}
}

#endif
