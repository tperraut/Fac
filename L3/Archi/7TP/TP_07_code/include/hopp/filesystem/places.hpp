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


#ifndef HOPP_FILESYSTEM_PLACES_HPP
#define HOPP_FILESYSTEM_PLACES_HPP

/**
 * @defgroup hopp_filesystem_places Places
 * @brief Filesystem functions about places (home directory)
 * @ingroup hopp_filesystem
 */

#include "../except.hpp"

#ifdef hopp_unix
	#include <unistd.h>
	#include <sys/stat.h>
	#include <sys/types.h>
	#include <pwd.h>
	#include <dirent.h>
#endif

#ifdef hopp_windows
	#include <Windows.h>
	#include <Shlobj.h>
	#include <Shlwapi.h>
#endif


namespace hopp
{
	namespace filesystem
	{
		/**
		 * @brief Get home directory
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @return the home directory
		 *
		 * @ingroup hopp_filesystem_places
		 */
		inline std::string home()
		{
			#ifdef hopp_unix
			
				struct passwd const * const pw = getpwuid(getuid());
				return pw->pw_dir;
				
			#elif hopp_windows
				
				// http://stackoverflow.com/questions/9542611/how-to-get-the-current-users-home-directory-in-windows
				// http://msdn.microsoft.com/en-us/library/windows/desktop/bb762181.aspx
				wchar_t path_wchar[MAX_PATH];
				SHGetFolderPathW(NULL, CSIDL_PROFILE, NULL, 0, path_wchar);
				
				// http://www.cplusplus.com/forum/general/39766/
				char path_char[MAX_PATH * 8];
				char char_def = ' ';
				WideCharToMultiByte(CP_ACP, 0, path_wchar, -1, path_char, 260, &char_def, NULL);
				
				return path_char;
				
			#else
				
				char const * const r = std::getenv("HOME");
				if (r != nullptr) { return r; }
				
				throw hopp::except::incomplete_implementation("hopp::filesystem::home is not implemented on your platform, please write a bug report or send a mail https://gitorious.org/hopp");
				
			#endif
		}
	}
}

#endif
