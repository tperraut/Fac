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


#ifndef HOPP_FILESYSTEM_PROPERTIES_HPP
#define HOPP_FILESYSTEM_PROPERTIES_HPP

/**
 * @defgroup hopp_filesystem_properties Properties
 * @brief Properties of files and directories
 * @ingroup hopp_filesystem
 */

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
		 * @brief Test if path is a file
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] path Path of the supposed file
		 *
		 * @return true if the path is a file, false otherwise
		 *
		 * @ingroup hopp_filesystem_properties
		 */
		inline bool is_a_file(std::string const & path)
		{
			#ifdef hopp_unix
				
				struct stat s;
				stat(path.c_str(), &s);
				
				if ((s.st_mode & S_IFMT) == S_IFREG) { return true; }
				else { return false; }
				
			#elif hopp_windows
				
				// http://msdn.microsoft.com/en-us/library/bb773621%28VS.85%29.aspx
				return (PathIsDirectory(path.c_str()) == false);
				
			#else
				
				throw hopp::except::incomplete_implementation("hopp::filesystem::is_a_file is not implemented on your platform, please write a bug report or send a mail https://gitorious.org/hopp");
				
			#endif
		}
		
		/**
		 * @brief Return true if we can read the file, false otherwise
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname Pathname of the file
		 *
		 * @return true if we can read the file, false otherwise
		 *
		 * @ingroup hopp_filesystem_properties
		 */
		inline bool file_is_readable(std::string const & pathname)
		{
			return hopp::filesystem::file_exists(pathname);
		}
		
		/**
		 * @brief Return true if we can write the file, false otherwise
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname Pathname of the file
		 *
		 * @return true if we can write the file, false otherwise
		 *
		 * @ingroup hopp_filesystem_properties
		 */
		inline bool file_is_writeable(std::string const & pathname)
		{
			if (hopp::filesystem::file_exists(pathname))
			{
				std::ofstream f(pathname, std::ofstream::out | std::ofstream::app);
				return bool(f);
			}
			else
			{
				return false;
			}
		}
		
		/**
		 * @brief Test if path is a directory
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] path Path of the supposed directory
		 *
		 * @return true if the path is a directory, false otherwise
		 *
		 * @ingroup hopp_filesystem_properties
		 */
		inline bool is_a_directory(std::string const & path)
		{
			#ifdef hopp_unix
				
				struct stat s;
				stat(path.c_str(), &s);
				
				if ((s.st_mode & S_IFMT) == S_IFDIR) { return true; }
				else { return false; }
				
			#elif hopp_windows
				
				// http://msdn.microsoft.com/en-us/library/bb773621%28VS.85%29.aspx
				return PathIsDirectory(path.c_str());
				
			#else
				
				throw hopp::except::incomplete_implementation("hopp::filesystem::is_a_directory is not implemented on your platform, please write a bug report or send a mail https://gitorious.org/hopp");
				
			#endif
		}
		
		/**
		 * @brief Test if path is executable
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] path Path
		 * 
		 * @note One Microsoft Windows, an executable is a file with "exe" extension
		 *
		 * @return true if the path is executable, false otherwise
		 *
		 * @ingroup hopp_filesystem_properties
		 */
		inline bool is_executable(std::string const & path)
		{
			#ifdef hopp_unix
				
				return (access(path.c_str(), X_OK) == 0);
				
			#elif hopp_windows
				
				return (hopp::filesystem::extension(path) == "exe");
				
			#else
				
				throw hopp::except::incomplete_implementation("hopp::filesystem::is_executable is not implemented on your platform, please write a bug report or send a mail https://gitorious.org/hopp");
				
			#endif
		}
	}
}

#endif
