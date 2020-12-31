CXX :=			g++
FLAGS :=		-std=c++17 -Og -gdwarf-4 -fno-omit-frame-pointer \
				-fno-strict-aliasing -fno-rtti -fno-exceptions \
				-Wall -Wextra -Wpedantic -Wshadow -Wcast-align -Wcast-qual \
				-Wconversion -Wsign-conversion -Wmissing-declarations \
				-Wredundant-decls

%.o:			%.cc
				$(CXX) $(FLAGS) -c -o $@ $<

prep:			prep.o
				$(CXX) $(FLAGS) -o prep prep.o

Checker:		Checker.agda Parser.agda Fast.agda Correct.agda
				agda --ghc Checker.agda

clean:
				rm -f prep prep.o
				rm -f Checker
				rm -rf _build MAlonzo
