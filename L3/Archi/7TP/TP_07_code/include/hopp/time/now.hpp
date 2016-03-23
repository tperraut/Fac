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


#ifndef HOPP_TIME_NOW_HPP
#define HOPP_TIME_NOW_HPP

/**
 * @defgroup hopp_time_now Current time
 * @copydoc hopp::now
 * @ingroup hopp_time
 */

#include <chrono>

#include "duration.hpp"


namespace hopp
{
	/**
	 * @brief Get current time (with std::chrono::steady_clock)
	 *
	 * http://en.cppreference.com/w/cpp/chrono/steady_clock/now
	 *
	 * @code
	   #include <hopp/time.hpp>
	   @endcode
	 */
	namespace now
	{
		/// @brief Same as std::chrono::steady_clock::now().time_since_epoch()
		/// @return std::chrono::steady_clock::now().time_since_epoch()
		/// @ingroup hopp_time_now
		inline
		auto now() -> decltype(std::chrono::steady_clock::now().time_since_epoch())
		{
			return std::chrono::steady_clock::now().time_since_epoch();
		}
		
		///  @brief Time (with std::chrono::steady_clock) in nanoseconds
		/// @return time (with std::chrono::steady_clock) in nanoseconds
		/// @ingroup hopp_time_now
		template <class T = double>
		T nanoseconds()
		{
			return hopp::duration::nanoseconds<T>(hopp::now::now());
		}
		
		/// @brief Time (with std::chrono::steady_clock) in microseconds
		/// @return time (with std::chrono::steady_clock) in microseconds
		/// @ingroup hopp_time_now
		template <class T = double>
		T microseconds()
		{
			return hopp::duration::microseconds<T>(hopp::now::now());
		}
		
		/// @brief Time (with std::chrono::steady_clock) in milliseconds
		/// @return time (with std::chrono::steady_clock) in milliseconds
		/// @ingroup hopp_time_now
		template <class T = double>
		T milliseconds()
		{
			return hopp::duration::milliseconds<T>(hopp::now::now());
		}
		
		/// @brief Time (with std::chrono::steady_clock) in seconds
		/// @return time (with std::chrono::steady_clock) in seconds
		/// @ingroup hopp_time_now
		template <class T = double>
		T seconds()
		{
			return hopp::duration::seconds<T>(hopp::now::now());
		}
		
		/// @brief Time (with std::chrono::steady_clock) in minutes
		/// @return time (with std::chrono::steady_clock) in minutes
		/// @ingroup hopp_time_now
		template <class T = double>
		T minutes()
		{
			return hopp::duration::minutes<T>(hopp::now::now());
		}
		
		/// @brief Time (with std::chrono::steady_clock) in hours
		/// @return time (with std::chrono::steady_clock) in hours
		/// @ingroup hopp_time_now
		template <class T = double>
		T hours()
		{
			return hopp::duration::hours<T>(hopp::now::now());
		}
	}
}

#endif
