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


#ifndef HOPP_PRINT_PRINT_HPP
#define HOPP_PRINT_PRINT_HPP

#include <iostream>
#include <mutex>


namespace hopp
{
	// print_ostream
	
	/// @brief End of hopp::print_ostream (call std::flush)
	/// @param[in] out An output stream (like std::ostream)
	/// @ingroup hopp_print
	template <class ostream_t>
	void print_ostream(ostream_t & out)
	{
		out << std::flush;
	}
	
	/// @brief Print all arguments in an output stream
	/// @param[in] out  An output stream (like std::ostream)
	/// @param[in] arg  First argument
	/// @param[in] args Other arguments
	/// @ingroup hopp_print
	template <class ostream_t, class T, class ... args_t>
	void print_ostream(ostream_t & out, T const & arg, args_t const & ... args)
	{
		out << arg;
		hopp::print_ostream(out, args...);
	}
	
	// print_ostream_mutex
	
	/// @brief Print all arguments in an output stream (thread-safe)
	/// @param[in] out  An output stream (like std::ostream)
	/// @param[in] args Arguments
	/// @ingroup hopp_print
	template <class ostream_t, class ... args_t>
	void print_ostream_mutex(ostream_t & out, args_t const & ... args)
	{
		static std::mutex mutex;
		mutex.lock();
		hopp::print_ostream(out, args...);
		mutex.unlock();
	}
	
	// print
	
	/// @brief Print all arguments in std::cout
	/// @param[in] args Arguments
	/// @ingroup hopp_print
	template <class ... args_t>
	void print(args_t const & ... args)
	{
		hopp::print_ostream(std::cout, args...);
	}
	
	// print_mutex
	
	/// @brief Print all arguments in std::cout
	/// @param[in] args Arguments
	/// @ingroup hopp_print
	template <class ... args_t>
	void print_mutex(args_t const & ... args)
	{
		hopp::print_ostream_mutex(std::cout, args...);
	}
}

#endif
