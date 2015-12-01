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


#ifndef HOPP_GEOMETRY_IS_INSIDE_HPP
#define HOPP_GEOMETRY_IS_INSIDE_HPP

#include "rectangle.hpp"
#include "../container/vector2.hpp"


namespace hopp
{
	namespace geometry
	{
		// Rectangle
		
		/**
		 * @brief Test if a point is inside the rectangle
		 *
		 * @code
		   #include <hopp/geometry.hpp>
		   @endcode
		 *
		 * @param[in] x         X coordinate of the point
		 * @param[in] y         Y coordinate of the point
		 * @param[in] rectangle A hopp::rectangle
		 *
		 * @return true if the point { x, y } is inside the rectangle, false otherwise
		 *
		 * @ingroup hopp_geometry
		 * @relates hopp::rectangle
		 */
		template <class T>
		bool is_inside(T const & x, T const & y, hopp::rectangle<T> const & rectangle)
		{
			return
			(
				x >= rectangle.left && x <= rectangle.left + rectangle.width &&
				y >= rectangle.top && y <= rectangle.top + rectangle.height
			);
		}
		
		/**
		 * @brief Test if a point is inside the rectangle
		 *
		 * @code
			#include <hopp/geometry.hpp>
		   @endcode
		 *
		 * @param[in] point     A hopp::vector2<T>
		 * @param[in] rectangle A hopp::rectangle
		 *
		 * @return true if the point { x, y } is inside the rectangle, false otherwise
		 *
		 * @ingroup hopp_geometry
		 * @relates hopp::rectangle
		 */
		template <class T>
		bool is_inside(hopp::vector2<T> const & point, hopp::rectangle<T> const & rectangle)
		{
			return hopp::geometry::is_inside(point.x, point.y, rectangle);
		}
	}
}

#endif
