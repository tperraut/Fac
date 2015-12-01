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


#ifndef HOPP_FILESYSTEM_DIRECTORY_HPP
#define HOPP_FILESYSTEM_DIRECTORY_HPP

/**
 * @defgroup hopp_filesystem_directory Directory
 * @brief Filesystem functions about directories
 * @ingroup hopp_filesystem
 */

#include <vector>

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

#include "../except.hpp"


namespace hopp
{
	namespace filesystem
	{
		/**
		 * @brief List all files and directories of a directory
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] path Path of the directory
		 *
		 * @return the list of files and directories
		 *
		 * @ingroup hopp_filesystem_directory
		 */
		inline std::vector<std::string> read_directory(std::string const & path)
		{
			// http://stackoverflow.com/questions/612097/how-can-i-get-a-list-of-files-in-a-directory-using-c-or-c
			
			#ifdef hopp_unix
				
				std::vector<std::string> r;
				
				DIR * dir = opendir(path.c_str());
				
				if (dir != nullptr)
				{
					struct dirent * ent = nullptr;
					
					while ((ent = readdir(dir)) != nullptr)
					{
						r.emplace_back(ent->d_name);
					}
					
					closedir(dir);
				}
				
				return r;
				
			#elif hopp_windows
				
				std::vector<std::string> r;
				
				WIN32_FIND_DATA find_file_data;
				HANDLE h_find = FindFirstFile((path + "/*").c_str(), &find_file_data);
				
				while (h_find != INVALID_HANDLE_VALUE)
				{
					r.emplace_back(find_file_data.cFileName);
					
					if (FindNextFile(h_find, &find_file_data) == 0)
					{
						FindClose(h_find);
						h_find = INVALID_HANDLE_VALUE;
					}
				}
				
				return r;
				
			#else
				
				throw hopp::except::incomplete_implementation("hopp::filesystem::read_directory is not implemented on your platform, please write a bug report or send a mail https://gitorious.org/hopp");
				
			#endif
		}
		
		/**
		 * @brief Create a directory
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] path Path of the directory
		 *
		 * @return true if directory is created, false otherwise
		 *
		 * @ingroup hopp_filesystem_directory
		 */
		inline bool create_directory(std::string const & path)
		{
			#ifdef hopp_unix
			
				// http://linux.die.net/man/3/mkdir
				int const status = mkdir(path.c_str(), S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH);
				return (status == 0);
				
			#elif hopp_windows
				
				// http://stackoverflow.com/questions/8931196/createdirectory-windows-api-usage-in-c
				// http://msdn.microsoft.com/en-us/library/windows/desktop/aa363855%28v=vs.85%29.aspx
				auto const r = CreateDirectory(path.c_str(), NULL);
				return bool(r);
				
			#else
				
				throw hopp::except::incomplete_implementation("hopp::filesystem::create_directory is not implemented on your platform, please write a bug report or send a mail https://gitorious.org/hopp");
				
			#endif
		}
	}
}

#endif
