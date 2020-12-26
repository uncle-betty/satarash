CXX :=			g++

FLAGS :=		-std=c++14 -Og -gdwarf-4 -fno-strict-aliasing \
				-Wall -Wextra -Wpedantic -Wshadow -Wcast-align -Wcast-qual \
				-Wconversion -Wsign-conversion -Wmissing-declarations \
				-Wredundant-decls

CXXFLAGS :=		$(FLAGS)
LDFLAGS :=		$(FLAGS)

DIR :=			$(shell pwd)
OBJS :=			prep.o
EXE :=			prep

%.o:			%.cc
				$(CXX) $(CXXFLAGS) -c -o $@ $<

$(EXE):			$(OBJS)
				$(CXX) $(LDFLAGS) -o $(EXE) $(OBJS)

val:			$(EXE)
				valgrind \
					--leak-check=full --leak-resolution=high \
					--show-leak-kinds=all --keep-stacktraces=alloc-and-free \
					$(DIR)/$(EXE)

run:			$(EXE)
				$(DIR)/$(EXE)

clean:
				rm -f $(EXE) $(OBJS)
