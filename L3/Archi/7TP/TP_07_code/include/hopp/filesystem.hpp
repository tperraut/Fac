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


#ifndef HOPP_FILESYSTEM_HPP
#define HOPP_FILESYSTEM_HPP

/**
 * @defgroup hopp_filesystem Filesystem
 * @copydoc hopp::filesystem
 */

#include "filesystem/directory.hpp"
#include "filesystem/directory_separator.hpp"
#include "filesystem/file.hpp"
#include "filesystem/filename.hpp"
#include "filesystem/places.hpp"
#include "filesystem/properties.hpp"


namespace hopp
{
	/**
	 * @brief Basic manipulation of files and directory
	 *
	 * @code
	   #include <hopp/filesystem.hpp>
	   @endcode
	 *
	 * @note The default directory separator is '/', use hnc::filesystem::directory_separator to change it
	 *
	 * @note Consider Boost.Filesystem and C++17
	 */
	namespace filesystem
	{
		// Just for Doxygen
	}
}

#endif
