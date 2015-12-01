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


#ifndef HOPP_FILESYSTEM_FILE_HPP
#define HOPP_FILESYSTEM_FILE_HPP

/**
 * @defgroup hopp_filesystem_file File
 * @brief Filesystem functions about files
 * @ingroup hopp_filesystem
 */

#include <fstream>

#ifdef hopp_unix
	#include <unistd.h>
	#include <sys/stat.h>
	#include <sys/types.h>
	#include <pwd.h>
	#include <dirent.h>
#endif

#include "filename.hpp"
#include "../compiler/unused.hpp"


namespace hopp
{
	namespace filesystem
	{
		/**
		 * @brief Return true if the file exists, false otherwise
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname Pathname of the file
		 *
		 * @return true if the file exists, false otherwise
		 *
		 * @ingroup hopp_filesystem_file
		 */
		inline bool file_exists(std::string const & pathname)
		{
			std::ifstream f(pathname);
			return bool(f);
		}
		
		/**
		 * @brief Remove a file (with remove function from cstdio)
		 *
		 * http://www.cplusplus.com/reference/cstdio/remove/
		 * 
		 * @param[in] pathname Pathname
		 *
		 * @ingroup hopp_filesystem_file
		 */
		inline void remove(std::string const & pathname)
		{
			std::remove(pathname.c_str());
		}
		
		/**
		 * @brief Copy a file
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 *
		 * @ingroup hopp_filesystem_file
		 * http://stackoverflow.com/questions/10195343/copy-a-file-in-an-sane-safe-and-efficient-way
		 *
		 * @param[in] source_filename      Source filename
		 * @param[in] destination_filename Destination filename
		 *
		 * @ingroup hopp_filesystem_file
		 */
		inline void copy_file(std::string const & source_filename, std::string const & destination_filename)
		{
			std::ifstream source(source_filename, std::ios::binary);
			std::ofstream destination(destination_filename, std::ios::binary);
			
			destination << source.rdbuf();
		}
		
		/**
		 * @brief Read whole text file
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * http://insanecoding.blogspot.fr/2011/11/how-to-read-in-file-in-c.html
		 *
		 * @param[in] filename Text filename
		 *
		 * @return A std::string that contains the whole text file. If file is not ok, returns empty string
		 *
		 * @ingroup hopp_filesystem_file
		 */
		inline std::string read_file(std::string const & filename)
		{
			std::ifstream f(filename, std::ios::in | std::ios::binary);
			
			// File ok
			if (f)
			{
				// Get the size
				f.seekg(0, std::ios::end);
				std::string r(size_t(f.tellg()), '\0');
				
				// Rewind the file
				f.seekg(0, std::ios::beg);
				
				// Read (and close) the file
				f.read(&r[0], std::streamsize(r.size()));
				f.close();
				
				// Return
				return r;
			}
			// File not ok
			else
			{
				return std::string();
			}
		}
		
		/**
		 * @brief Return a temporary filename (with tmpnam function from cstdio)
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * http://www.cplusplus.com/reference/cstdio/tmpnam/
		 *
		 * @return the temporary filename
		 *
		 * @ingroup hopp_filesystem_file
		 */
		inline std::string tmp_filename()
		{
			// mkstemp
			#ifdef hopp_unix
			
				// Generate filename
				char filename_buffer[] = "/tmp/XXXXXXXX\0";
				int r = mkstemp(filename_buffer);
				hopp_unused(r);
				std::string const filename = filename_buffer;
				
			// std::tmpnam
			#else
				
				// Generate filename
				char filename_buffer[L_tmpnam];
				std::tmpnam(filename_buffer);
				std::string const filename = filename_buffer;
				
				// fopen and fclose file (else fstream does not work...)
				FILE * f = std::fopen(filename.c_str(), "w");
				std::fclose(f);
				
			#endif
			
			// Return
			return filename;
		}
		
		/**
		 * @brief Return an available filename based on user's proposition (no safe in multi-thread context)
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname_wanted Pathname wanted
		 * @param[in] separator       Separator between pathname wanted and number is the function generate a filename
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return a available filename
		 *
		 * @ingroup hopp_filesystem_file
		 */
		inline std::string filename_without_overwrite
		(
			std::string const & pathname_wanted,
			std::string const & separator = "_",
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// File does not exist
			if (hopp::filesystem::file_exists(pathname_wanted) == false)
			{
				return pathname_wanted;
			}
			// File exists
			else
			{
				// Find the next available pathname
				std::string available_pathname;
				unsigned int i = 0;
				do
				{
					available_pathname = hopp::filesystem::add_suffix(pathname_wanted, separator + std::to_string(i), directory_separator);
					++i;
				}
				while (hopp::filesystem::file_exists(available_pathname) == true);
				// Return
				return available_pathname;
			}
		}
	}
}

#endif
