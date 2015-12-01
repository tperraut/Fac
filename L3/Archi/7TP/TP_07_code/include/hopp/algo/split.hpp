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


#ifndef HOPP_ALGO_SPLIT_HPP
#define HOPP_ALGO_SPLIT_HPP

#include <algorithm>
#include <iterator>
#include <vector>

#include "../compiler/unused.hpp"


namespace hopp
{
	/// @brief Split the container by a delimiter
	/// @param[in] c                Container like std::vector, std::string, std::list
	/// @param[in] first            Iterator to the first element
	/// @param[in] last             Iterator to the last element (not included)
	/// @param[in] delimiter        Delimiter
	/// @param[in] return_container Returned container (to stock the chunks) (std::vector by default)
	/// @return a container with all chunks
	/// @ingroup hopp_algo
	template <class container_t, class return_container_t = std::vector<container_t>>
	return_container_t split
	(
		container_t const & c,
		typename container_t::const_iterator first, typename container_t::const_iterator const & last,
		typename container_t::value_type const & delimiter,
		return_container_t return_container = return_container_t()
	)
	{
		hopp_unused(c);
		
		using const_iterator_t = typename container_t::const_iterator;
		const_iterator_t it_0 = first;
		const_iterator_t it_1 = last;
		
		while (it_0 != last)
		{
			it_1 = std::find(it_0, last, delimiter);
			
			// Copy the range
			return_container.push_back(container_t(it_0, it_1));
			
			// Delimiter found
			if (it_1 != last)
			{
				// Next
				it_0 = std::next(it_1, 1);
				
				// Actual position is the last value
				if (it_0 == last)
				{
					// Add empty container_t
					return_container.push_back(container_t());
				}
			}
			
			// End (it_1 == last)
			else
			{
				it_0 = last;
			}
		}

		return return_container;
	}
	
	/// @brief Split the container with a delimiter
	/// @param[in] c                Container like std::vector, std::string, std::list
	/// @param[in] delimiter        Delimiter
	/// @param[in] return_container Returned container (to stock the chunks) (std::vector by default)
	/// @return a container with all chunks
	/// @ingroup hopp_algo
	template <class container_t, class return_container_t = std::vector<container_t>>
	return_container_t split
	(
		container_t const & c,
		typename container_t::value_type const & delimiter,
		return_container_t return_container = return_container_t()
	)
	{
		return hopp::split(c, std::begin(c), std::end(c), delimiter, return_container);
	}
}

#endif
