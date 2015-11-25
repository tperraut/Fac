Installation (With CMake)
-------------------------

mkdir build
cd build
cmake .. # -DCMAKE_INSTALL_PREFIX=/path/to/install # -DDEBUG=TRUE # -DDISABLE_TESTS=TRUE
make
# make doxygen
# make test
make install # su -c "make install" # sudo make install
