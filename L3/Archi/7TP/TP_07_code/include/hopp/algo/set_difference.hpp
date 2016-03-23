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


#ifndef HOPP_ALGO_SET_DIFFERENCE_HPP
#define HOPP_ALGO_SET_DIFFERENCE_HPP

#include <algorithm>
#include <stdexcept>


namespace hopp
{
	namespace algo
	{
		/**
		 * @brief Set the difference between two sorted containers using std::set_difference
		 *
		 * @code
		   #include <hopp/algo.hpp>
		   @endcode
		 *
		 * @param[in] container_0 First container
		 * @param[in] container_1 Second container
		 *
		 * @pre container_0 and container_1 are sorted
		 *
		 * Example:
		 * @code
		   std::vector<int> a = { 0, 1, 2, 3, 4, 5 };
		   std::list<int>   b = {    1,       4, 5, 6, 7, 8, 9 };
		   
		   std::sort(a.begin(), a.end());
		   b.sort();
		   
		   std::vector<int> const r = hopp::algo::set_difference(a, b);
		   
		   std::cout << r << std::endl; // 0, 2, 3
		   @endcode
		 *
		 * @ingroup hopp_algo
		 */
		template <class container_t0, class container_t1>
		container_t0 set_difference
		(
			container_t0 const & container_0,
			container_t1 const & container_1
		)
		{
			#ifndef NDEBUG
			if (std::is_sorted(container_0.begin(), container_0.end()) == false) { throw std::invalid_argument("hopp::algo::set_difference: container_0 is not sorted"); }
			if (std::is_sorted(container_1.begin(), container_1.end()) == false) { throw std::invalid_argument("hopp::algo::set_difference: container_1 is not sorted"); }
			#endif
			
			container_t0 r = container_0;
			
			auto const it = std::set_difference(container_0.begin(), container_0.end(), container_1.begin(), container_1.end(), r.begin());
			
			r.resize(size_t(it - r.begin()));
			
			return r;
		}
	}
}

#endif
