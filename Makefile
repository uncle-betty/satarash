MODE :=			1

CXX :=			g++
CXX_FLAGS :=	-std=c++17 -Og -gdwarf-4 -fno-omit-frame-pointer \
				-fno-strict-aliasing -fno-rtti -fno-exceptions \
				-Wall -Wextra -Wpedantic -Wshadow -Wcast-align -Wcast-qual \
				-Wconversion -Wsign-conversion -Wmissing-declarations \
				-Wredundant-decls

ifeq ($(MODE), 0)
GHC_FLAGS :=	--ghc-flag=-prof --ghc-flag=-fprof-auto
else ifeq ($(MODE), 1)
GHC_FLAGS :=	--ghc-flag=-O2
else ifeq ($(MODE), 2)
GHC_FLAGS :=	--ghc-flag=-O2 --ghc-flag=-fspecialize-aggressively \
					--ghc-flag=-fexpose-all-unfoldings
else
GHC_FLAGS :=
endif

TOP :=			src/Satarash/Checker.agda
ALL :=			$(wildcard src/Satarash/*.agda)

%.o:			%.cc
				$(CXX) $(CXX_FLAGS) -c -o $@ $<

checker:		checker.o
				$(CXX) $(CXX_FLAGS) -o checker checker.o

Checker:		$(ALL)
				agda --ghc $(GHC_FLAGS) --compile-dir=. $(TOP)

check:
				agda -isrc src/Everything.agda

clean:
				rm -f checker checker.o
				rm -f Checker
				rm -rf _build MAlonzo
