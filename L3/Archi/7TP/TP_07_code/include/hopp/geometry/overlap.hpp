// Copyright © 2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_GEOMETRY_OVERLAP_HPP
#define HOPP_GEOMETRY_OVERLAP_HPP

#include "rectangle.hpp"
#include "is_inside.hpp"


namespace hopp
{
	namespace geometry
	{
		/**
		 * @brief Check the intersection between two rectangles
		 *
		 * @code
		   #include <hopp/geometry.hpp>
		   @endcode
		 *
		 * @param[in] a A hopp::rectangle
		 * @param[in] b A hopp::rectangle
		 *
		 * @return true if rectangles overlap, false otherwise
		 *
		 * @ingroup hopp_geometry
		 * @relates hopp::rectangle
		 */
		template <class T>
		bool overlap(hopp::rectangle<T> const & a, hopp::rectangle<T> const & b)
		{
			if (hopp::geometry::is_inside(a.left, a.top, b)) { return true; }
			if (hopp::geometry::is_inside(a.right(), a.top, b)) { return true; }
			if (hopp::geometry::is_inside(a.left, a.bottom(), b)) { return true; }
			if (hopp::geometry::is_inside(a.right(), a.bottom(), b)) { return true; }
			
			if (hopp::geometry::is_inside(b.left, b.top, a)) { return true; }
			if (hopp::geometry::is_inside(b.right(), b.top, a)) { return true; }
			if (hopp::geometry::is_inside(b.left, b.bottom(), a)) { return true; }
			if (hopp::geometry::is_inside(b.right(), b.bottom(), a)) { return true; }
			
			return false;
		}
	}
}

#endif
