// Copyright © 2013, 2014 Inria, Written by Lénaïc Bagnères, lenaic.bagneres@inria.fr
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


#ifndef HOPP_FILESYSTEM_DIRECTORY_SEPARATOR_HPP
#define HOPP_FILESYSTEM_DIRECTORY_SEPARATOR_HPP


namespace hopp
{
	namespace filesystem
	{
		/**
		 * @brief Directory separator (e.g. '/' by default, '/' on GNU/Linux and all (including Windows), '\' for Windows only)
		 *
		 * The default directory separator is '/', works on GNU/Linux, Unix and Windows
		 *
		 * http://en.wikipedia.org/wiki/Path_%28computing%29
		 *
		 * @ingroup hopp_filesystem_directory
		 */
		namespace directory_separator
		{
			/// @brief Default (common) directory separator: GNU/Linux, Unix, BSD, Android, MAC OS X, ... and Windows
			constexpr char const common = '/';
			
			/// @brief Directory separator for Windows only
			constexpr char const windows = '\\';
			
			/// @brief Directory separator for Classic Mac OS
			constexpr char const classic_mac_os = ':';
			
			/// @brief Directory separator for TOPS-20, RSX-11, OpenVMS, RISC OS, NonStop Kernel
			constexpr char const dot = '.';
			
			/// @brief Directory separator for Stratus VOS
			constexpr char const greater_than = '>';
		}
	}
}

#endif
