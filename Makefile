CXX :=			g++
FLAGS :=		-std=c++17 -Og -gdwarf-4 -fno-omit-frame-pointer \
				-fno-strict-aliasing -fno-rtti -fno-exceptions \
				-Wall -Wextra -Wpedantic -Wshadow -Wcast-align -Wcast-qual \
				-Wconversion -Wsign-conversion -Wmissing-declarations \
				-Wredundant-decls

%.o:			%.cc
				$(CXX) $(FLAGS) -c -o $@ $<

checker:		checker.o
				$(CXX) $(FLAGS) -o checker checker.o

Checker:		Checker.agda Parser.agda Verifier.agda
				agda --ghc Checker.agda

clean:
				rm -f checker checker.o
				rm -f Checker
				rm -rf _build MAlonzo
