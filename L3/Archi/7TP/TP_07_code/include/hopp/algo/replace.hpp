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


#ifndef HOPP_ALGO_REPLACE_HPP
#define HOPP_ALGO_REPLACE_HPP

#include <algorithm>
#include <iterator>

#include "find_range.hpp"
#include "replace_range.hpp"


namespace hopp
{
	/// @brief Replace the first values by others between two iterators
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
	container_t & replace
	(
		container_t & c, typename container_t::iterator first, typename container_t::iterator last,
		container_t const & old_values, container_t const & new_values
	)
	{
		auto it = hopp::find_range(first, last, old_values);
		
		if (it != last)
		{
			hopp::replace_range(c, it, std::next(it, std::ptrdiff_t(old_values.size())), new_values.begin(), new_values.end());
		}
		
		return c;
	}

	/// @brief Replace the first values by others in a container
	/// @param[in,out] c          Container like std::vector, std::list
	/// @param[in]     old_values Container with values to be replaced
	/// @param[in]     new_values Container with replacement values
	/// @return the container
	/// @note Consider std::replace to replace one element by one other element
	/// @ingroup hopp_algo
	template <class container_t>
	container_t & replace(container_t & c, container_t const & old_values, container_t const & new_values)
	{
		return hopp::replace(c, std::begin(c), std::end(c), old_values, new_values);
	}

	/// @brief Replace the first values by others in a container
	/// @param[in] c          Container like std::vector, std::list
	/// @param[in] old_values Container with values to be replaced
	/// @param[in] new_values Container with replacement values
	/// @return a container after replace
	/// @note Consider Boost.Range
	/// @note Consider std::replace to replace one element by one other element
	/// @ingroup hopp_algo
	template <class container_t>
	container_t replace_copy(container_t const & c, container_t const & old_values, container_t const & new_values)
	{
		container_t r = c;
		hopp::replace(r, std::begin(r), std::end(r), old_values, new_values);
		return r;
	}
}

#endif
