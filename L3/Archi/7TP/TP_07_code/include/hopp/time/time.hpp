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


#ifndef HOPP_TIME_TIME_HPP
#define HOPP_TIME_TIME_HPP

#include <chrono>

#include "duration.hpp"


namespace hopp
{
	/**
	 * @brief Class to measure intervals
	 *
	 * @code
	   #include <hopp/time.hpp>
	   @endcode
	 *
	 * http://en.cppreference.com/w/cpp/chrono/steady_clock
	 *
	 * @b Example:
	 * @code
	   // Start
	   hopp::time time;
	   
	   // Do something
	   
	   // End
	   time.end();
	   
	   // Time
	   std::cout << "Time = " << time.nanoseconds() << " nanoseconds" << std::endl;
	   std::cout << "Time = " << time.microseconds() << " microseconds" << std::endl;
	   std::cout << "Time = " << time.milliseconds() << " milliseconds" << std::endl;
	   std::cout << "Time = " << time.seconds() << " seconds" << std::endl;
	   std::cout << "Time = " << time.minutes() << " minutes" << std::endl;
	   std::cout << "Time = " << time.hours() << " hours" << std::endl;
	   @endcode
	 *
	 * @ingroup hopp_time
	 */
	class time
	{
	public:
		
		/// Type of std::chrono::steady_clock::now()
		using now_t = decltype(std::chrono::steady_clock::now());
		
		/// Duration type
		using duration_t = decltype(now_t() - now_t());
		
	private:
		
		/// Start
		now_t m_start;
		
		/// End
		now_t m_end;
		
		/// Duration
		duration_t m_duration;
		
	public:
		
		/// @brief Constructor
		time() { start(); }
		
		/// @brief Start
		void start() { m_start = std::chrono::steady_clock::now(); }
		
		/// @brief End
		void end() { m_end = std::chrono::steady_clock::now(); m_duration = m_end - m_start; }
		
		/// @brief Restart
		/// @return the hopp::time restarted to get duration, seconds, ...
		hopp::time const & restart() { end(); start(); return *this; }
		
		/// @brief Get duration
		duration_t duration() const { return m_duration; }
		
		/// @brief Get measured time in nanoseconds
		/// @return Measured time in nanoseconds
		template <class T = double>
		T nanoseconds() const { return hopp::duration::nanoseconds<T>(duration()); }
		
		/// @brief Get measured time in microseconds
		/// @return Measured time in microseconds
		template <class T = double>
		T microseconds() const { return hopp::duration::microseconds<T>(duration()); }
		
		/// @brief Get measured time in milliseconds
		/// @return Measured time in milliseconds
		template <class T = double>
		T milliseconds() const { return hopp::duration::milliseconds<T>(duration()); }
		
		/// @brief Get measured time in seconds
		/// @return Measured time in seconds
		template <class T = double>
		T seconds() const { return hopp::duration::seconds<T>(duration()); }
		
		/// @brief Get measured time in minutes
		/// @return Measured time in minutes
		template <class T = double>
		T minutes() const { return hopp::duration::minutes<T>(duration()); }
		
		/// @brief Get measured time in hours
		/// @return Measured time in hours
		template <class T = double>
		T hours() const { return hopp::duration::hours<T>(duration()); }
	};
}

#endif
