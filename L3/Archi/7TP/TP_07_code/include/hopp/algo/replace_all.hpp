// Copyright © 2013-2015 Lénaïc Bagnères, hnc@singularity.fr

// This file is part of hnc.

// hnc is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// hnc is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with hnc. If not, see <http://www.gnu.org/licenses/>


#ifndef HOPP_ALGO_REPLACE_ALL_HPP
#define HOPP_ALGO_REPLACE_ALL_HPP

#include <algorithm>
#include <iterator>

#include "find_range.hpp"
#include "replace_range.hpp"


namespace hopp
{
	/// @brief Replace all values by others between two iterators
	/// @param[in,out] c          Container like std::vector, std::list
	/// @param[in]     first      Iterator to the first element
	/// @param[in]     last       Iterator to the last element (not included)
	/// @param[in]     old_values Container with values to be replaced
	/// @param[in]     new_values Container with replacement values
	/// @return the container
	/// @note Consider Boost.Range
	/// @note Consider std::replace to replace one element by one other element
	/// @ingroup hopp_algo
	template <class container_t>
	container_t & replace_all
	(
		container_t & c, typename container_t::iterator first, typename container_t::iterator last,
		container_t const & old_values, container_t const & new_values
	)
	{
		auto it = hopp::find_range(first, last, old_values);
		
		while (it != last)
		{
			// Replace can invalidate the iterator
			auto distance_begin_it = std::distance(c.begin(), it);
			auto distance_it_last = std::distance(it, last);
			
			hopp::replace_range(c, it, std::next(it, std::ptrdiff_t(old_values.size())), new_values.begin(), new_values.end());
			
			// Resume and advance iterators
			if (old_values.size() < new_values.size())
			{
				it = std::next(c.begin(), distance_begin_it + std::ptrdiff_t(new_values.size()) - std::ptrdiff_t(old_values.size()) + 1);
				last = std::next(it, distance_it_last - 1);
			}
			else if (old_values.size() > new_values.size())
			{
				it = std::next(c.begin(), distance_begin_it);
				last = std::next(it, distance_it_last - std::ptrdiff_t(old_values.size() - new_values.size()));
			}
			else // Same size
			{
				std::advance(it, old_values.size());
			}
			
			// Next replace
			it = hopp::find_range(it, last, old_values);
		}
		
		return c;
	}

	/// @brief Replace all values by others in a container
	/// @param[in,out] c          Container like std::vector, std::list
	/// @param[in]     old_values Container with values to be replaced
	/// @param[in]     new_values Container with replacement values
	/// @return the container
	/// @note Consider Boost.Range
	/// @note Consider std::replace to replace one element by one other element
	/// @ingroup hopp_algo
	template <class container_t>
	container_t & replace_all(container_t & c, container_t const & old_values, container_t const & new_values)
	{
		return hopp::replace_all(c, c.begin(), c.end(), old_values, new_values);
	}

	/// @brief Replace all values by others in a container
	/// @param[in] c          Container like std::vector, std::list
	/// @param[in] old_values Container with values to be replaced
	/// @param[in] new_values Container with replacement values
	/// @return a container after replaces
	/// @note Consider Boost.Range
	/// @note Consider std::replace to replace one element by one other element
	/// @ingroup hopp_algo
	template <class container_t>
	container_t replace_all_copy(container_t const & c, container_t const & old_values, container_t const & new_values)
	{
		container_t r = c;
		hopp::replace_all(r, r.begin(), r.end(), old_values, new_values);
		return r;
	}
}

#endif
