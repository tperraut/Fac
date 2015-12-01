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


#ifndef HOPP_STREAM_GET_LINE_HPP
#define HOPP_STREAM_GET_LINE_HPP

#include <istream>
#include <string>
#include <vector>

#include "get_until.hpp"


namespace hopp
{
	/// @brief Get line until a delimiter from delimiters
	/// @param[in,out] in         A std::istream
	/// @param[out]    line       Line
	/// @param[in]     delimiters Delimiters
	/// @return the std::istream
	/// @ingroup hopp_stream
	inline std::istream & get_line(std::istream & in, std::string & line, std::vector<char> const & delimiters)
	{
		hopp::get_until(in, line, delimiters);
		in.get();
		return in;
	}
}

#endif
