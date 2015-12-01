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


#ifndef HOPP_FILESYSTEM_FILENAME_HPP
#define HOPP_FILESYSTEM_FILENAME_HPP

/**
 * @defgroup hopp_filesystem_filename Filename
 * @brief Filesystem functions about file names
 *
 * @image html hopp_filesystem.png
 * @image latex hopp_filesystem.eps
 *
 * @ingroup hopp_filesystem
 */

#include <string>
#include <algorithm>

#include "directory_separator.hpp"


namespace hopp
{
	namespace filesystem
	{
		/**
		 * @brief Return the filename of a pathname
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname            Pathname
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return the filename of a pathname
		 *
		 * @ingroup hopp_filesystem_filename
		 */
		inline std::string filename
		(
			std::string const & pathname,
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// Get last separator
			auto it = std::find(pathname.rbegin(), pathname.rend(), directory_separator);
			// Separator found
			if (it != pathname.rend())
			{
				return std::string(it.base(), pathname.end());
			}
			// No separator found
			else
			{
				return pathname;
			}
		}
		
		/**
		 * @brief Return the dirname of a pathname (without the final directory separator)
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname            Pathname
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return the dirname of a pathname (without the final directory separator)
		 *
		 * @ingroup hopp_filesystem_filename
		 */
		inline std::string dirname
		(
			std::string const & pathname,
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// Get last separator
			auto it = std::find(pathname.rbegin(), pathname.rend(), directory_separator);
			// Separator found
			if (it != pathname.rend())
			{
				++it;
				return std::string(pathname.begin(), it.base());
			}
			// No separator found
			else
			{
				return "";
			}
		}
		
		/**
		 * @brief Return the basename of a pathname
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname            Pathname
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return the basename of a pathname
		 *
		 * @ingroup hopp_filesystem_filename
		 */
		inline std::string basename
		(
			std::string const & pathname,
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// Get filename
			std::string filename = hopp::filesystem::filename(pathname, directory_separator);
			// Get last separator
			auto it = std::find(filename.rbegin(), filename.rend(), '.');
			// Separator found
			if (it != filename.rend())
			{
				++it;
				return std::string(filename.begin(), it.base());
			}
			// No separator found
			else
			{
				return filename;
			}
		}
		
		/**
		 * @brief Return the dirname and the basename of a pathname
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname            Pathname
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return the dirname and the basename of a pathname
		 *
		 * @ingroup hopp_filesystem_filename
		 */
		inline std::string dir_and_basename
		(
			std::string const & pathname,
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// Dirname
			std::string dirname = hopp::filesystem::dirname(pathname, directory_separator);
			// Basename
			std::string basename = hopp::filesystem::basename(pathname, directory_separator);
			
			// Return
			if (dirname.empty()) { return basename; }
			else if (basename.empty()) { return dirname + directory_separator; }
			else { return dirname + directory_separator + basename; }
		}
		
		/**
		 * @brief Return the extension of a file (without the '.')
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname            Pathname
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return the extension of a file (without the '.')
		 *
		 * @ingroup hopp_filesystem_filename
		 */
		inline std::string extension
		(
			std::string const & pathname,
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// Get filename
			std::string filename = hopp::filesystem::filename(pathname, directory_separator);
			// Get last separator
			auto it = std::find(filename.rbegin(), filename.rend(), '.');
			// Separator found
			if (it != filename.rend())
			{
				return std::string(it.base(), filename.end());
			}
			// No separator found
			else
			{
				return "";
			}
		}
		
		/**
		 * @brief Add prefix (before the basename, after the dirname)
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname            Pathname
		 * @param[in] prefix              Prefix to add
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return the pathname with the prefix
		 *
		 * @ingroup hopp_filesystem_filename
		 */
		inline std::string add_prefix
		(
			std::string const & pathname,
			std::string const & prefix,
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// Get dirname with separator
			std::string const dirname = [&pathname, &directory_separator]() -> std::string
			{
				std::string r = hopp::filesystem::dirname(pathname);
				if (r != "") { r += directory_separator; }
				return r;
			}();
			// Get basename
			std::string const basename = hopp::filesystem::basename(pathname);
			// Get extension with .
			std::string const extension = [&pathname]() -> std::string
			{
				std::string r = hopp::filesystem::extension(pathname);
				if (r != "") { r = "." + r; }
				return r;
			}();
			// Return
			return dirname + prefix + basename + extension;
		}
		
		/**
		 * @brief Add suffix (after the basename, before the extension)
		 *
		 * @code
		   #include <hopp/filesystem.hpp>
		   @endcode
		 *
		 * @param[in] pathname            Pathname
		 * @param[in] suffix              Suffix to add
		 * @param[in] directory_separator Directory separator char (hopp::filesystem::directory_separator::common by default)
		 *
		 * @return the pathname with the suffix
		 *
		 * @ingroup hopp_filesystem_filename
		 */
		inline std::string add_suffix
		(
			std::string const & pathname,
			std::string const & suffix,
			char const directory_separator = hopp::filesystem::directory_separator::common
		)
		{
			// Get dirname with separator
			std::string const dirname = [&pathname, &directory_separator]() -> std::string
			{
				std::string r = hopp::filesystem::dirname(pathname);
				if (r != "") { r += directory_separator; }
				return r;
			}();
			// Get basename
			std::string const basename = hopp::filesystem::basename(pathname);
			// Get extension with .
			std::string const extension = [&pathname]() -> std::string
			{
				std::string r = hopp::filesystem::extension(pathname);
				if (r != "") { r = "." + r; }
				return r;
			}();
			// Return
			return dirname + basename + suffix + extension;
		}
	}
}

#endif
