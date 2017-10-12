# A template C++ Makefile for your SAT solver.

# Debugging flags
#FLAGS=-Wall -Wold-style-cast -Wformat=2 -ansi -pedantic -ggdb3 \
-DDEBUG

# Optimizing flags
FLAGS= -std=c++14 -Wall -Wold-style-cast -Wformat=2 -ansi -pedantic -O3

# List all the .o files you need to build here
OBJS=parser.o toysat.o

# This is the name of the executable file that gets built.  Please
# don't change it.
EXENAME=toysat

# Compile targets
all: $(OBJS)
	g++ $(FLAGS) $(OBJS) -lz -o $(EXENAME)
parser.o: parser.cpp parser.h
	g++ $(FLAGS) -c parser.cpp
sat.o: toysat.cpp parser.h
	g++ $(FLAGS) -c toysat.cpp

# Add more compilation targets here



# The "phony" `clean' compilation target.  Type `make clean' to remove
# your object files and your executable.
.PHONY: clean
clean:
	rm -rf $(OBJS) $(EXENAME)
