// Copyright © 2012-2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_CONTAINER_INDEX_HPP
#define HOPP_CONTAINER_INDEX_HPP

/**
 * @defgroup hopp_container_index Index
 * @brief Index conversion
 * @ingroup hopp_container
 */

#include <iostream>
#include <stdexcept>


namespace hopp
{
	/// @brief To manipulate 2D index
	/// @ingroup hopp_container_index
	namespace index2D
	{
		/**
		 * @brief Transform a 2D index (i, j) into an index 1D (i * nb_row + j)
		 *
		 * @code
		   #include <hopp/container/index2D.hpp>
		   @endcode
		 * 
		 * @param[in] i      Row index
		 * @param[in] j      Column index
		 * @param[in] nb_row Number of rows
		 *
		 * @pre The size of the row must be >= 1
		 *
		 * @exception std::out_of_range if i >= nb_row
		 *
		 * @return index 1D (i * nb_row + j)
		 *
		 * @ingroup hopp_container_index
		 */
		template <class index_t>
		index_t index1D(index_t const i, index_t const j, index_t const nb_row)
		{
			#ifndef NDEBUG
				if (i >= nb_row) { throw std::out_of_range("hopp::index2D::index1D: i >= nb_row"); }
			#endif
			
			return (i * nb_row + j);
		}
	}
}

#endif
