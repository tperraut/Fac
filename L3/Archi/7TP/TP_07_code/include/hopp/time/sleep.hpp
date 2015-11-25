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


#ifndef HOPP_TIME_SLEEP_HPP
#define HOPP_TIME_SLEEP_HPP

/**
 * @defgroup hopp_time_sleep Sleep
 * @copydoc hopp::sleep
 * @ingroup hopp_time
 */

#include <thread>


namespace hopp
{
	/**
	 * @brief Sleep functions
	 *
	 * @code
	   #include <hopp/time.hpp>
	   @endcode
	 *
	 * @b Example:
	 * @code
	   std::cout << "Sleep for 500'000'000 nanoseconds" << std::endl;
	   hopp::sleep::nanoseconds(500000000);
	   
	   std::cout << "Sleep for 500'000 microseconds" << std::endl;
	   hopp::sleep::microseconds(500000);
	   
	   std::cout << "Sleep for 500 milliseconds" << std::endl;
	   hopp::sleep::milliseconds(500);
	   
	   std::cout << "Sleep for 1 seconds" << std::endl;
	   hopp::sleep::seconds(1);
	   
	   //std::cout << "Sleep for 1 minutes" << std::endl;
	   //hopp::sleep::minutes(1);
	   
	   //std::cout << "Sleep for 1 hours" << std::endl;
	   //hopp::sleep::hours(1);
	   @endcode
	 */
	namespace sleep
	{
		/// @brief Sleep some nanoseconds
		/// @param[in] ns Number of nanoseconds
		/// @ingroup hopp_time_sleep
		inline
		void nanoseconds(unsigned int const ns)
		{
			std::this_thread::sleep_for(std::chrono::nanoseconds(ns));
		}
		
		/// @brief Sleep some microseconds
		/// @param[in] us Number of microseconds
		///  @ingroup hopp_time_sleep
		inline
		void microseconds(unsigned int const us)
		{
			std::this_thread::sleep_for(std::chrono::microseconds(us));
		}
		
		/// @brief Sleep some milliseconds
		/// @param[in] ms Number of milliseconds
		/// @ingroup hopp_time_sleep
		inline
		void milliseconds(unsigned int const ms)
		{
			std::this_thread::sleep_for(std::chrono::milliseconds(ms));
		}
		
		/// @brief Sleep some seconds
		/// @param[in] s Number of seconds
		/// @ingroup hopp_time_sleep
		inline
		void seconds(unsigned int const s)
		{
			std::this_thread::sleep_for(std::chrono::seconds(s));
		}
		
		/// @brief Sleep some minutes
		/// @param[in] m Number of minutes
		/// @ingroup hopp_time_sleep
		inline
		void minutes(unsigned int const m)
		{
			std::this_thread::sleep_for(std::chrono::minutes(m));
		}
		
		/// @brief Sleep some hours
		/// @param[in] h Number of hours
		/// @ingroup hopp_time_sleep
		inline
		void hours(unsigned int const h)
		{
			std::this_thread::sleep_for(std::chrono::hours(h));
		}
	}
}

#endif
