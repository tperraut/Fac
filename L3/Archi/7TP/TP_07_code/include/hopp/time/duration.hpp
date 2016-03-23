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


#ifndef HOPP_TIME_DURATION_HPP
#define HOPP_TIME_DURATION_HPP

/**
 * @defgroup hopp_time_duration Duration conversion
 * @copydoc hopp::duration
 * @ingroup hopp_time
 */

#include <chrono>
#include <ratio>


namespace hopp
{
	/**
	 * @brief Conversion of a duration to nanoseconds, ..., seconds, ..., hours, ...
	 *
	 * @code
	   #include <hopp/time.hpp>
	   @endcode
	 *
	 * http://en.cppreference.com/w/cpp/chrono/duration
	 */
	namespace duration
	{
		/// @brief Conversion of a duration to nanoseconds
		/// @param[in] duration A duration
		/// @return duration as nanoseconds
		/// @ingroup hopp_time_duration
		template <class T = double, class duration_t>
		T nanoseconds(duration_t const & duration) { return std::chrono::duration<T, std::nano>(duration).count(); }
		
		/// @brief Conversion of a duration to microseconds
		/// @param[in] duration A duration
		/// @return duration as microseconds
		/// @ingroup hopp_time_duration
		template <class T = double, class duration_t>
		T microseconds(duration_t const & duration) { return std::chrono::duration<T, std::micro>(duration).count(); }
		
		/// @brief Conversion of a duration to milliseconds
		/// @param[in] duration A duration
		/// @return duration as milliseconds
		/// @ingroup hopp_time_duration
		template <class T = double, class duration_t>
		T milliseconds(duration_t const & duration) { return std::chrono::duration<T, std::milli>(duration).count(); }
		
		/// @brief Conversion of a duration to seconds
		/// @param[in] duration A duration
		/// @return duration as seconds
		/// @ingroup hopp_time_duration
		template <class T = double, class duration_t>
		T seconds(duration_t const & duration) { return std::chrono::duration<T>(duration).count(); }
		
		/// @brief Conversion of a duration to minutes
		/// @param[in] duration A duration
		/// @return duration as minutes
		/// @ingroup hopp_time_duration
		template <class T = double, class duration_t>
		T minutes(duration_t const & duration) { return std::chrono::duration<T, std::ratio<60>>(duration).count(); }
		
		/// @brief Conversion of a duration to hours
		/// @param[in] duration A duration
		/// @return duration as hours
		/// @ingroup hopp_time_duration
		template <class T = double, class duration_t>
		T hours(duration_t const & duration) { return std::chrono::duration<T, std::ratio<3600>>(duration).count(); }
	}
}

#endif
