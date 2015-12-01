// Copyright © 2015 Rodolphe Cargnello, rodolphe.cargnello@gmail.com
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


#ifndef HOPP_PARSER_INI_HPP
#define HOPP_PARSER_INI_HPP

#include <fstream>

#include "../stream/ignore_whitespaces.hpp"
#include "../stream/ignore_line.hpp"
#include "../stream/get_line.hpp"
#include "../stream/get_until.hpp"
#include "../string/remove_multiple_whitespaces.hpp"
#include "../string/remove_trailing_whitespaces.hpp"
#include "../container/vector_pair.hpp"


namespace hopp
{
	
	namespace parser
	{
		/// @brief Parse INI file https://en.wikipedia.org/wiki/INI_file
		/// @param[in] filename INI filename
		/// @return a hopp::vector_pair<std::string, hopp::vector_pair<std::string, std::string>>
		/// @ingroup hopp_parser
		inline hopp::vector_pair<std::string, hopp::vector_pair<std::string, std::string>> ini(std::string const & filename)
		{
			std::ifstream file(filename);
			
			hopp::vector_pair<std::string, hopp::vector_pair<std::string, std::string>> r;
			
			std::string section;
			
			while (file.good())
			{
				hopp::ignore_whitespaces(file); if (file.good() == false) { break; }
				
				if (char(file.peek()) == ';' || char(file.peek()) == '#')
				{
					hopp::ignore_line(file);
					continue;
				}
				
				// Section
				if (char(file.peek()) == '[')
				{
					file.get();
					hopp::ignore_whitespaces(file);
					std::getline(file, section, ']');
					hopp::remove_trailing_whitespaces(section);
					hopp::ignore_line(file);
					continue;
				}
				
				// Key
				std::string key;
				std::getline(file, key, '=');
				hopp::remove_trailing_whitespaces(key);
				
				// Value
				std::string value;
				hopp::ignore_whitespaces(file);
				hopp::get_until(file, value, { ';', '#', '\n' });
				hopp::remove_trailing_whitespaces(value);
				hopp::ignore_line(file);
				
				// Add
				r[section].push_back(key, value);
			}
			
			return r;
		}
	}
}

#endif
