# Variables
CC = gcc
CD = make_coredump.sh
CFLAGS = -Wall -Wextra -O2
SRC = is_symbolic.c
OBJ_DIR = bin
OBJ = $(OBJ_DIR)/is_symbolic

# Default target: compile the binary into bin/
all: $(OBJ_DIR) $(OBJ)

# Create bin/ directory if it doesn't exist
$(OBJ_DIR):
	mkdir -p $(OBJ_DIR)

# Compile is_symbolic.c and place the binary in bin/
$(OBJ): $(SRC)
	$(CC) $(CFLAGS) -o $(OBJ) $(SRC)
	$(CD) $(OBJ).snapshot $(OBJ)

# Clean up the compiled binary
clean:
	rm -f $(OBJ)
	rm -f $(OBJ).snapshot

# Prevent make from confusing clean with a file called clean
.PHONY: clean
