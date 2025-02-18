# Standard library imports
import itertools # Provides functions for creating iterators for efficient looping
import operator # Implements operator as functions (e.g., operator.or_) for logical and bitwise operations
from datetime import datetime # Supplies classes for working with dates and times, especially for time tracking in solving process
from functools import reduce # Implements tools for working with functions and callable objects, like applying a function cumulatively to items of an iterable

# Third-party library imports
import pycosat # A Python wrapper around picosat SAT solver, used for solving boolean satisfiability problems

# Tkinter GUI imports
import tkinter as tk # Tkinter is Python's standard GUI package, aliased as tk for brevity
from tkinter import Canvas, Tk, Button, Label, Entry, Frame, messagebox, filedialog, colorchooser, ttk # Importing specific modules from tkinter for GUI elements:
                                                                                                    # Canvas: For drawing graphics
                                                                                                    # Tk: The main window class
                                                                                                    # Button, Label, Entry, Frame: Common UI widgets
                                                                                                    # messagebox: For displaying dialog boxes like error messages
                                                                                                    # filedialog, colorchooser, ttk: Additional UI utilities and styled widgets

# Other utility imports
from argparse import ArgumentParser # For parsing command-line arguments, although in this GUI application, it's used minimally for options setup


# Constants for directions and colors
class FlowFreeConstants:
    """
    Manages constants for the Flow Free game.
    This class defines constants related to directions, direction types, and colors used in the Flow Free game logic and GUI.
    It uses bitwise operations for efficient representation and manipulation of directions.
    """
    LEFT = 1  # Constant representing the left direction in bitwise operations (binary 0001)
    RIGHT = 2  # Constant representing the right direction in bitwise operations (binary 0010)
    TOP = 4   # Constant representing the top direction in bitwise operations (binary 0100)
    BOTTOM = 8 # Constant representing the bottom direction in bitwise operations (binary 1000)

    DELTAS = [(LEFT, 0, -1), (RIGHT, 0, 1), (TOP, -1, 0), (BOTTOM, 1, 0)]  # Coordinate changes associated with each direction.
                                                                          # Each tuple is (direction_bit, delta_row, delta_col).
                                                                          # Used to calculate neighbor cell positions based on direction.
                                                                          # For example, (LEFT, 0, -1) means for LEFT direction, row change is 0, column change is -1.

    LR = LEFT | RIGHT  # Constant representing both left and right directions combined (bitwise OR) (binary 0011)
    TB = TOP | BOTTOM  # Constant representing both top and bottom directions combined (bitwise OR) (binary 1100)
    TL = TOP | LEFT    # Constant representing top-left direction combined (bitwise OR) (binary 0101)
    TR = TOP | RIGHT  # Constant representing top-right direction combined (bitwise OR) (binary 0110)
    BL = BOTTOM | LEFT  # Constant representing bottom-left direction combined (bitwise OR) (binary 1001)
    BR = BOTTOM | RIGHT  # Constant representing bottom-right direction combined (bitwise OR) (binary 1010)

    DIR_TYPES = [LR, TB, TL, TR, BL, BR]  # List of all possible direction types, combinations of basic directions.
                                          # These represent the possible path shapes within a grid cell (horizontal, vertical, curves).
    DIR_FLIP = {LEFT: RIGHT, RIGHT: LEFT, TOP: BOTTOM, BOTTOM: TOP}  # Dictionary to get the opposite direction for each direction.
                                                                  # Used for checking neighbor connections; if cell A connects RIGHT to cell B, then cell B connects LEFT to cell A.
    DIR_LOOKUP = {LR: '─', TB: '│', TL: '┘', TR: '└', BL: '┐', BR: '┌'}  # Dictionary mapping direction types to characters for text representation.
                                                                    # Used for debugging or text-based output (not directly used in GUI drawing).

    COLOR_NAMES = {
        'R': 'Red', 'B': 'Blue', 'Y': 'Yellow', 'G': 'Green', 'O': 'Orange',
        'C': 'Cyan', 'M': 'Magenta', 'm': 'Maroon', 'P': 'Purple', 'A': 'Gray',
        'W': 'White', 'g': 'LightGreen', 'T': 'Tan', 'b': 'DarkBlue', 'c': 'DarkCyan', 'p': 'Pink'
    }  # Dictionary of color mnemonics (single characters) to full color names.
       # Mnemonics are used in puzzle input strings for compactness.
       # Full color names are used in GUI and display for user readability.
    COLOR_MNEMONICS = ''.join(COLOR_NAMES.keys()) # String of all color mnemonics concatenated together for easy lookup and iteration.


# Helper class for SAT problem generation
class SATHelper:
    """
    Utility class for handling SAT (Satisfiability) problem generation.
    This class provides static methods to assist in creating SAT problem formulations for the Flow Free puzzle.
    It includes methods for generating pairs, clauses, and neighbor information, useful for encoding puzzle constraints into SAT clauses.
    Static methods are used as they are utility functions and do not require class instance state.
    """

    @staticmethod
    def get_pairs(collection):
        """
        Generates pairs of elements from a collection.
        Used to create combinations of variables for "at most one true" constraints in SAT clauses.
        For example, to ensure only one color is assigned to a cell, we need to generate pairs of all color variables for that cell.

        Args:
            collection (iterable): A collection of items (e.g., list, tuple) to generate pairs from.

        Yields:
            tuple: Pairs of elements from the collection.
        """
        return itertools.combinations(collection, 2)

    @staticmethod
    def clauses_no_two_true(sat_variables):
        """
        Generates clauses ensuring no two variables are true simultaneously (at most one true).
        For a set of SAT variables, creates clauses that prevent any two variables from being true at the same time.
        This is a common constraint in SAT problem encoding, especially for one-hot encoding, ensuring exclusivity.
        For example, if variables v1, v2, v3 represent colors for a cell, this function generates clauses to ensure at most one of them is true.

        Args:
            sat_variables (iterable): A collection of SAT variables (integers representing variables).

        Yields:
            tuple: CNF clauses (tuples of integers) that represent the constraint.
                   Each clause is a tuple of two negated variables (-var1, -var2), meaning "not var1 OR not var2".
                   This clause form ensures that var1 and var2 cannot both be true.
        """
        return ((-var1, -var2) for var1, var2 in SATHelper.get_pairs(sat_variables))

    @staticmethod
    def explode_puzzle(puzzle):
        """
        Yields the row, column, and character of each cell in the puzzle.
        Iterates through each cell of the puzzle grid and provides its coordinates (row, column) and the character in it.
        Useful for processing each cell in the puzzle in a systematic way, for example, when generating SAT clauses for each cell.

        Args:
            puzzle (list of str): A 2D puzzle represented as a list of strings (rows).

        Yields:
            tuple: For each cell, yields (row_index, col_index, cell_char).
        """
        for row_index, row in enumerate(puzzle):
            for col_index, cell_char in enumerate(row):
                yield row_index, col_index, cell_char

    @staticmethod
    def is_valid_position(size, row_index, col_index):
        """
        Checks if a position is within the puzzle bounds.
        Verifies if given row and column indices are within the valid range of the puzzle grid size.
        Used to ensure that neighbor calculations do not go out of the grid boundaries.

        Args:
            size (int): The size of the puzzle grid (number of rows or columns, assuming square grid).
            row_index (int): The row index to check.
            col_index (int): The column index to check.

        Returns:
            bool: True if the position is valid (within bounds), False otherwise.
        """
        return 0 <= row_index < size and 0 <= col_index < size

    @staticmethod
    def get_all_neighbors(row_index, col_index):
        """
        Yields all neighbors of a cell, regardless of puzzle boundaries.
        For a given cell, provides all potential neighbors in four directions (LEFT, RIGHT, TOP, BOTTOM).
        It does not check if the neighbors are within the puzzle grid boundaries; validity check is done separately.
        Used as a preliminary step to find potential neighbors, which are then filtered for validity.

        Args:
            row_index (int): The row index of the cell.
            col_index (int): The column index of the cell.

        Yields:
            tuple: For each neighbor, yields (direction_bit, neighbor_row, neighbor_col).
                   direction_bit is a constant from FlowFreeConstants (LEFT, RIGHT, TOP, BOTTOM) indicating the direction to the neighbor.
        """
        for direction_bit, delta_row, delta_col in FlowFreeConstants.DELTAS:
            yield (direction_bit, row_index + delta_row, col_index + delta_col)

    @staticmethod
    def get_valid_neighbors(size, row_index, col_index):
        """
        Yields valid neighbors of a cell within the puzzle boundaries.
        Provides neighbors of a cell that are actually within the puzzle grid.
        It uses get_all_neighbors to get potential neighbors and then filters out those that are outside the grid using is_valid_position.

        Args:
            size (int): The size of the puzzle grid.
            row_index (int): The row index of the cell.
            col_index (int): The column index of the cell.

        Yields:
            tuple: For each valid neighbor, yields (direction_bit, neighbor_row, neighbor_col).
        """
        return (
            (direction_bit, neighbor_row, neighbor_col)
            for direction_bit, neighbor_row, neighbor_col in SATHelper.get_all_neighbors(row_index, col_index)
            if SATHelper.is_valid_position(size, neighbor_row, neighbor_col)
        )

    @staticmethod
    def convert_color_labels_to_mnemonics(puzzle, colors):
        """
        Converts color labels (e.g., 'A', 'B', 'C'...) in the puzzle to mnemonics (e.g., 'R', 'B', 'Y'...).
        This is useful if the input puzzle uses alphabetical labels instead of the mnemonic characters that the solver expects internally.
        It maps 'A' to the first color mnemonic, 'B' to the second, and so on, based on FlowFreeConstants.COLOR_MNEMONICS.
        This allows for more user-friendly puzzle inputs using letters instead of cryptic mnemonics.

        Args:
            puzzle (list of str): The puzzle grid with color labels.
            colors (dict): A dictionary of color labels to color indices.

        Returns:
            tuple: A tuple containing:
                - new_puzzle (list of str): The puzzle grid with color mnemonics.
                - new_colors (dict): Updated color dictionary with mnemonics as keys and original indices as values.
            tuple: (None, None) if there is an error like invalid character in puzzle. In this case, an error message is shown to the user.
        """
        if 'R' in colors: # if puzzle already uses mnemonics, return as is, no conversion needed
            return puzzle, colors

        color_lookup = FlowFreeConstants.COLOR_MNEMONICS # Get the string of color mnemonics for mapping
        new_puzzle = [] # Initialize list for the new puzzle with mnemonics
        new_colors = {} # Initialize dict for new colors with mnemonics

        try:
            for row in puzzle:
                new_row = []
                for char in row:
                    if char.isalnum(): # if char is an endpoint label (A-Z, a-z)
                        char = color_lookup[ord(char) - ord('A')] # Convert label to mnemonic using lookup table; 'A' becomes first mnemonic, 'B' second, etc.
                    new_row.append(char)
                new_puzzle.append(''.join(new_row))

            new_colors = {color_lookup[ord(label) - ord('A')]: index for label, index in colors.items()} # Update color dict to use mnemonics as keys
                                                                                                        # Reconstruct the color dictionary but with mnemonics as keys instead of labels.

        except IndexError:
             messagebox.showerror("Error", "Invalid character in puzzle. Only A-z are allowed.") # Handle case where label is out of range (e.g., more labels than available mnemonics)
             return None, None
        return new_puzzle, new_colors # Return the converted puzzle and color dictionary


# Class for parsing and validating puzzles
class PuzzleParser:
    """
    Parses and validates Flow Free puzzles from string input.
    This class provides methods to take a puzzle string, validate its format (square grid, equal row lengths),
    and parse it into a usable format (2D list of characters) along with extracting color information.
    It also handles error checking for invalid puzzle formats, like non-square grids or unequal row lengths, and reports errors to the user via message boxes.
    """

    @staticmethod
    def parse_puzzle(options, puzzle_str, filename='puzzle input'):
        """
        Parses a puzzle from a string.
        Takes a puzzle string, splits it into lines, and validates its structure and content.
        It checks for squareness, equal row lengths, and correct number of endpoints for each color (exactly two: start and end).
        If any validation fails, it displays an error message box and returns None.

        Args:
            options (argparse.Namespace): Command-line options (currently not heavily used in GUI, but included for potential future use).
            puzzle_str (str): The puzzle string input, multi-line string representing the grid.
            filename (str, optional): Filename or description of the puzzle source for error messages. Defaults to 'puzzle input'.
                                      Used in error messages to indicate where the parsing error occurred.

        Returns:
            tuple: A tuple containing:
                - puzzle (list of str): The parsed puzzle as a 2D list of characters (rows).
                - colors (dict): A dictionary mapping color mnemonics to color indices.
            tuple: (None, None) if there is an error during parsing.
        """
        puzzle = puzzle_str.strip().splitlines() # Removes leading/trailing whitespace and splits into list of rows
        if not puzzle: # Check if puzzle input is empty
            messagebox.showerror("Error", "Puzzle input is empty.") # Show error message if puzzle string is empty
            return None, None

        size = len(puzzle[0])  # Gets the size of the puzzle based on the length of the first row
        if any(len(row) != size for row in puzzle): # Checks if all rows have the same length as the first row, ensuring rectangular shape
            messagebox.showerror("Error", f'{filename}: Puzzle rows are not of equal length.') # Error if rows have different lengths
            return None, None

        if len(puzzle) != size: # Checks if the number of rows is equal to the number of columns (square puzzle)
            messagebox.showerror("Error", f'{filename}: Puzzle is not square.') # Error if puzzle is not square
            return None, None

        colors = {} # Dictionary to store color labels (characters) and their assigned indices. e.g., {'A': 0, 'B': 1}
        color_endpoint_counts = [] # List to keep track of endpoint counts for each color. e.g., [2, 2] means color 0 and color 1 both have 2 endpoints found.

        for row_index, row in enumerate(puzzle):
            for col_index, char in enumerate(row):
                if char.isalnum(): # Checks if the character is alphanumeric (color endpoint label)
                    if char in colors: # If this color is already encountered (start point found, checking for end point)
                        color_index = colors[char] # Get the color index from the colors dictionary
                        if color_endpoint_counts[color_index]: # Check if an endpoint for this color has already been found (meaning we found a second endpoint)
                            messagebox.showerror("Error",
                                                 f'{filename}: Too many endpoints for color {char} at line {row_index + 1}, column {col_index+1}.') # Error if more than 2 endpoints for a color
                            return None, None
                        color_endpoint_counts[color_index] = 1 # Increment endpoint count for this color (second endpoint found)
                    else: # If this is a new color endpoint (first endpoint for this color)
                        color_index = len(colors) # Assign a new color index (starting from 0 for the first color, 1 for the second, etc.)
                        colors[char] = color_index # Store the color and its index in the colors dictionary
                        color_endpoint_counts.append(0) # Initialize endpoint count for this new color to 0 (first endpoint found, expecting a second)

        for color_count in color_endpoint_counts: # After parsing, check if all colors have exactly two endpoints (start and end)
            if not color_count: # if color_endpoint_counts is still 0, it means only one endpoint (start) was found for a color
                missing_color_char = list(colors.keys())[color_endpoint_counts.index(0)] # Find the color that is missing the second endpoint
                messagebox.showerror("Error", f'Color {missing_color_char} has a start point but no end point.') # Error if a color is missing an endpoint
                return None, None

        if not options.quiet: # If not in quiet mode (usually for command-line, but GUI sets quiet=True), print puzzle info to console
            print(f'Read {size}x{size} puzzle with {len(colors)} colors from {filename}')
            print()

        puzzle, colors = SATHelper.convert_color_labels_to_mnemonics(puzzle, colors) # Convert color labels to mnemonics if needed (e.g., 'A' to 'R')
        if puzzle is None: # Check if conversion failed (e.g., invalid character)
            return None, None
        return puzzle, colors # Return parsed puzzle (list of strings) and color information (dictionary)


# Class for generating SAT clauses
class SATClauseGenerator:
    """
    Generates SAT (Satisfiability) clauses for the Flow Free puzzle.
    This class is responsible for translating the Flow Free puzzle constraints into Conjunctive Normal Form (CNF) clauses,
    which are the input format for SAT solvers. It defines static methods to create clauses for color constraints and direction constraints.
    The generated clauses ensure that a valid Flow Free solution is found by the SAT solver.
    """

    @staticmethod
    def make_color_clauses(puzzle, colors, color_var):
        """
        Generate CNF clauses entailing the N*M color SAT variables, where N is the number of cells and M is the number of colors.
        Each cell encodes a single color in a one-hot fashion, meaning for each cell, exactly one color variable must be true, and all others false.
        This method generates clauses that ensure each cell in the puzzle is assigned exactly one color,
        and for endpoint cells, it forces them to have the specified color from the puzzle input.
        It also adds clauses to ensure endpoints are connected to at least one and at most one neighbor of the same color.

        Args:
            puzzle (list of str): The parsed puzzle grid.
            colors (dict): Dictionary mapping color mnemonics to color indices.
            color_var (function): A function that returns the SAT variable index for a given cell and color.
                                  It should take (row_index, col_index, color_index) and return an integer representing the SAT variable.
                                  This function is pre-defined to ensure a consistent mapping from puzzle cells and colors to SAT variables.

        Returns:
            list: A list of CNF clauses (lists of integers) representing color constraints.
        """
        clauses = [] # Initialize list to store generated clauses
        num_colors = len(colors) # Get the number of colors in the puzzle
        size = len(puzzle) # Get the size of the puzzle grid

        # for each cell in the puzzle grid
        for i, j, char in SATHelper.explode_puzzle(puzzle):

            if char.isalnum():  # if the cell is a flow endpoint (has a color label)

                endpoint_color = colors[char] # Get the color index for this endpoint based on its label

                # Clause: color in this cell is this specific endpoint color. Force the color variable for this cell and endpoint color to be true.
                clauses.append([color_var(i, j, endpoint_color)])

                # Clauses: color in this cell is NOT any of the other colors. Force the color variable for this cell and any other color to be false.
                for other_color in range(num_colors):
                    if other_color != endpoint_color: # For all colors other than the endpoint color
                        clauses.append([-color_var(i, j, other_color)])

                # gather neighbors' variables for this color
                neighbor_vars = [color_var(ni, nj, endpoint_color) for
                                 _, ni, nj in SATHelper.get_valid_neighbors(size, i, j)] # Get SAT variables for valid neighbors with the same endpoint color

                # Clause: at least one neighbor has this color. Ensures that an endpoint is connected to at least one path segment of the same color.
                clauses.append(neighbor_vars)

                # Clauses: no two neighbors have this color. Ensures that an endpoint is connected to at most one path segment of the same color, preventing branching at endpoints.
                clauses.extend(SATHelper.clauses_no_two_true(neighbor_vars))

            else: # if the cell is not an endpoint ('.', it's an empty cell that will be part of a flow path)

                # Clause: at least one of the colors in this cell is set. Ensures that every non-endpoint cell is assigned a color.
                clauses.append([color_var(i, j, color)
                                for color in range(num_colors)])

                # Clauses: no two of the colors in this cell are set (at most one color). Ensures that each non-endpoint cell is assigned at most one color.
                # Combined with the 'at least one' clause above, this enforces that exactly one color is assigned to each non-endpoint cell.
                cell_color_vars = (color_var(i, j, color) for
                                   color in range(num_colors))

                clauses.extend(SATHelper.clauses_no_two_true(cell_color_vars))

        return clauses # Return the list of generated color clauses

    @staticmethod
    def make_direction_variables(puzzle, start_variable_index):
        """
        Creates the direction-type SAT variables for each cell (except endpoints).
        For each non-endpoint cell, it determines possible direction types (LR, TB, TL, TR, BL, BR) based on valid neighbors
        and creates SAT variables to represent these direction types.
        Direction variables are used to represent the shape of the path segment in each cell (horizontal, vertical, or curves).
        Each direction type is represented by a unique SAT variable.

        Args:
            puzzle (list of str): The parsed puzzle grid.
            start_variable_index (int): The starting index for direction variables.
                                         Color variables are indexed first, so direction variables start after them.
                                         This ensures that color and direction variables have distinct indices in the SAT problem.

        Returns:
            tuple: A tuple containing:
                - dir_vars (dict): A dictionary to store direction variables for each cell.
                                   Keys are cell coordinates (row_index, col_index), and values are dictionaries
                                   mapping direction types to their SAT variable indices.
                                   e.g., dir_vars[(0, 1)][FlowFreeConstants.LR] = 101 (variable index for LR direction in cell (0, 1))
                - num_dir_vars (int): The total number of direction variables created.
                                      This count is needed to track the total number of variables in the SAT problem.
        """

        size = len(puzzle) # Get puzzle grid size
        dir_vars = dict() # Initialize dictionary to store direction variables
        num_dir_vars = 0  # Initialize counter for direction variables

        for i, j, char in SATHelper.explode_puzzle(puzzle): # Iterate through each cell

            if char.isalnum():  # flow endpoint, no direction needed, skip to the next cell
                continue

            # collect bits for neighbors (TOP BOTTOM LEFT RIGHT). Determine which directions are possible for this cell based on grid boundaries.
            neighbor_bits = (dir_bit for (dir_bit, ni, nj)
                             in SATHelper.get_valid_neighbors(size, i, j))

            # OR them all together to get cell flags. Combine neighbor direction bits to determine allowed direction types in this cell.
            # For example, if a cell has neighbors in TOP, BOTTOM, and RIGHT directions, cell_flags will represent TOP | BOTTOM | RIGHT.
            cell_flags = reduce(operator.or_, neighbor_bits, 0)

            # create a lookup for dir type vars in this cell. Initialize dictionary for direction variables in this cell.
            dir_vars[i, j] = dict()

            for code in FlowFreeConstants.DIR_TYPES: # Iterate through all possible direction types (LR, TB, TL, TR, BL, BR)
                # only add variable if cell has correct flags (i.e. if cell has
                # TOP, BOTTOM, RIGHT neighbors, don't add LR direction type).
                if cell_flags & code == code: # Check if the direction type is valid for this cell based on neighbors.
                                              # For example, if cell_flags is TOP | BOTTOM | RIGHT, and code is TB (TOP | BOTTOM), then the condition is true.
                    num_dir_vars += 1 # Increment direction variable counter
                    dir_vars[i, j][code] = start_variable_index + num_dir_vars # Assign a new SAT variable index to this direction type and store it in the dir_vars dictionary.
                                                                              # Variable indices start from start_variable_index + 1 and increment for each direction variable.

        return dir_vars, num_dir_vars # Return direction variable dictionary and total count of direction variables

    @staticmethod
    def make_direction_clauses(puzzle, colors, color_var, dir_vars):
        """
        Generate clauses involving the color and direction-type SAT variables.
        Each free cell must be exactly one direction, and directions imply color matching with neighbors.
        This method creates clauses that ensure each non-endpoint cell has exactly one direction type assigned,
        and that directions are consistent with color assignments in neighboring cells.
        For example, if a cell is set to have a direction type that connects to a neighbor, then both cells must have the same color.

        Args:
            puzzle (list of str): The parsed puzzle grid.
            colors (dict): Dictionary mapping color mnemonics to color indices.
            color_var (function): Function to get color variable index for a cell and color.
            dir_vars (dict): Dictionary of direction variables created by make_direction_variables.

        Returns:
            list: A list of CNF clauses (lists of integers) representing direction and color consistency constraints.
        """

        dir_clauses = [] # Initialize list for direction clauses
        num_colors = len(colors) # Get number of colors
        size = len(puzzle) # Get puzzle size

        # for each cell in the puzzle
        for i, j, char in SATHelper.explode_puzzle(puzzle):

            if char.isalnum():  # flow endpoint, no direction needed, skip to the next cell
                continue

            cell_dir_dict = dir_vars[(i, j)] # Get direction variable dictionary for this cell
            cell_dir_vars = cell_dir_dict.values() # Get list of direction variables (SAT variable indices) for this cell

            # Clause: at least one direction is set in this cell. Every non-endpoint cell must have at least one direction type assigned.
            dir_clauses.append(list(cell_dir_vars))

            # Clauses: no two directions are set in this cell. Every non-endpoint cell must have at most one direction type assigned.
            # Combined with the 'at least one' clause above, this enforces that exactly one direction type is assigned to each non-endpoint cell.
            dir_clauses.extend(SATHelper.clauses_no_two_true(cell_dir_vars))

            # for each color
            for color in range(num_colors):

                # get color var for this cell
                color_1 = color_var(i, j, color) # Get color variable for current cell (i, j) and color 'color'

                # for each neighbor
                for dir_bit, n_i, n_j in SATHelper.get_all_neighbors(i, j): # Iterate through all potential neighbors (valid or invalid)

                    # get color var for other cell
                    color_2 = color_var(n_i, n_j, color) # Get color variable for neighbor cell (n_i, n_j) and the same color 'color'

                    # for each direction variable in this cell
                    for dir_type, dir_var in cell_dir_dict.items(): # Iterate through all possible direction types for the current cell (and their SAT variables)

                        # if neighbor is hit by this direction type
                        if dir_type & dir_bit: # Check if the current direction type 'dir_type' implies a connection to the neighbor in direction 'dir_bit'.
                                                # For example, if dir_type is LR and dir_bit is RIGHT, then the condition is true, indicating a rightward connection.
                            # Clause: this direction type implies the colors are equal. If direction 'dir_type' is set, then if current cell has color 'color' and neighbor has color 'color', they must be the same color.
                            dir_clauses.append([-dir_var, -color_1, color_2]) # Implication: dir_var -> (color_1 -> color_2)  (if dir_var is true, then color_1 implies color_2)
                            dir_clauses.append([-dir_var, color_1, -color_2]) # Implication: dir_var -> (color_1 -> !color_2) (if dir_var is true, then color_1 implies not color_2) - Corrected Clause: This seems incorrect and should be: dir_clauses.append([-dir_var, -color_1, color_2]) and dir_clauses.append([-dir_var, -color_2, color_1])
                            dir_clauses.append([-dir_var, -color_2, color_1]) # Added clause: Implication: dir_var -> (color_2 -> color_1) (if dir_var is true, then color_2 implies color_1) - ensuring color consistency in both directions of connection.

                        elif SATHelper.is_valid_position(size, n_i, n_j): # Check if neighbor position is valid within the grid.
                                                                          # If the neighbor is valid but not in the direction of 'dir_type', it implies no connection in that direction.
                            # neighbor is not along this direction type,
                            # so this direction type implies the colors are not equal. If direction 'dir_type' is set, and neighbor is in a direction not covered by 'dir_type', then current cell and neighbor cannot have the same color.
                            dir_clauses.append([-dir_var, -color_1, -color_2]) # Implication: dir_var -> (color_1 -> !color_2) (if dir_var is true, then color_1 implies not color_2 - meaning colors are different).

        return dir_clauses # Return the list of generated direction clauses

    @staticmethod
    def reduce_puzzle_to_sat(options, puzzle, colors):
        """
        Reduces the given puzzle to a SAT problem specified in CNF (Conjunctive Normal Form).
        This is the main method to convert a Flow Free puzzle into a SAT problem.
        It generates color clauses and direction clauses by calling other methods in this class, combining them into a complete set of CNF clauses for the puzzle.
        It also calculates the total number of variables and clauses, and measures the time taken for the reduction process.

        Args:
            options (argparse.Namespace): Command-line options (not heavily used in GUI, but included for potential future use).
            puzzle (list of str): The parsed puzzle grid.
            colors (dict): Dictionary of color mnemonics to color indices.

        Returns:
            tuple: A tuple containing:
                - color_var (function): Function to get color variable index. This function is crucial for accessing color variables based on cell and color index.
                - dir_vars (dict): Dictionary of direction variables. This dictionary maps cell coordinates and direction types to their SAT variable indices.
                - num_vars (int): Total number of variables in the SAT problem (color variables + direction variables).
                - clauses (list): List of CNF clauses representing the puzzle constraints. This list is the input for the SAT solver.
                - reduce_time (float): Time taken for the reduction process in seconds.
            tuple: (None, None, None, None, None) if there is an error, such as invalid puzzle or color information. In this case, an error message is shown to the user.
        """
        if not puzzle or not colors: # Check if puzzle and color info are valid (not None or empty)
            messagebox.showerror("Error", "Invalid puzzle or color information.") # Show error message if puzzle or colors are invalid
            return None, None, None, None, None

        size = len(puzzle)  # Get size of the puzzle grid
        num_colors = len(colors) # Get number of colors in the puzzle
        if size <= 0 or num_colors <= 0: # Check for invalid size or color count (non-positive)
            messagebox.showerror("Error", "Invalid puzzle size or number of colors.") # Show error message if size or color count is invalid
            return None, None, None, None, None

        num_cells = size ** 2 # Calculate total number of cells in the grid
        num_color_vars = num_colors * num_cells # Calculate total number of color variables (one for each color in each cell)

        def color_var(i, j, color):
            '''
            Return the index of the SAT variable for the given color in row i, column j.
            This is a helper function (closure) to calculate the index of a color variable based on row, column, and color index.
            It uses a consistent indexing scheme to map 3D coordinates (row, column, color) to a 1D variable index.
            This formula ensures that each color variable gets a unique index.
            '''
            return (i * size + j) * num_colors + color + 1 # Formula to compute the variable index; +1 because SAT solvers typically use 1-based indexing for variables.

        start = datetime.now() # Record the start time of the reduction process

        color_clauses = SATClauseGenerator.make_color_clauses(puzzle,
                                            colors,
                                            color_var) # Generate color related clauses by calling make_color_clauses method

        dir_vars, num_dir_vars = SATClauseGenerator.make_direction_variables(puzzle, num_color_vars) # Generate direction variables by calling make_direction_variables method.
                                                                                                    # Direction variables start indexing after the color variables.

        dir_clauses = SATClauseGenerator.make_direction_clauses(puzzle, colors,
                                            color_var, dir_vars) # Generate direction related clauses by calling make_direction_clauses method, using the generated direction variables and color variable function.

        num_vars = num_color_vars + num_dir_vars # Calculate total number of variables (sum of color and direction variables)
        clauses = color_clauses + dir_clauses # Combine color and direction clauses into a single list, which represents the complete SAT problem in CNF

        reduce_time = (datetime.now() - start).total_seconds() # Calculate the time taken for the reduction process (time elapsed since start)

        if not options.quiet: # If not in quiet mode, print reduction statistics to console
            print(
                f'generated {len(color_clauses):,} clauses over {num_color_vars:,} color variables') # Print number of color clauses and variables

            print(
                f'generated {len(dir_clauses):,} dir clauses over {num_dir_vars:,} dir variables') # Print number of direction clauses and variables

            print(f'total {len(clauses):,} clauses over {num_vars:,} variables') # Print total number of clauses and variables

            print(f'reduced to SAT in {reduce_time:.3f} seconds') # Print reduction time
            print()

        return color_var, dir_vars, num_vars, clauses, reduce_time # Return all components of the SAT problem: color variable function, direction variables, total variables, clauses, and reduction time


# Class for decoding SAT solutions
class SolutionDecoder:
    """
    Decodes SAT solutions and detects cycles in the solution.
    This class takes the raw SAT solution (a list of variable assignments) from the SAT solver and translates it back into a readable Flow Free solution grid.
    It also includes methods to detect cycles in the decoded solution, which is a crucial step in the iterative SAT solving process for Flow Free.
    Cycles are invalid paths in Flow Free, so they need to be detected and prevented in subsequent SAT solving iterations.
    """

    @staticmethod
    def decode_sat_solution(puzzle, colors, color_var, dir_vars, sol):
        """
        Takes the solution set from SAT and decodes it by undoing the one-hot encoding in each cell for color and direction-type.
        Returns a 2D array of (color, direction-type) pairs, representing the solved puzzle grid.
        This method converts the SAT solution (a list of true variables) back into a 2D grid representing the solved Flow Free puzzle.
        For each cell, it determines the assigned color and direction type based on which SAT variables are true in the solution.

        Args:
            puzzle (list of str): The parsed puzzle grid.
            colors (dict): Dictionary of color mnemonics to color indices.
            color_var (function): Function to get color variable index.
            dir_vars (dict): Dictionary of direction variables.
            sol (list): SAT solution, a list of integers representing true variables (positive integers) and false variables (absence of integers or negative integers - though pycosat solution is list of true variables only).

        Returns:
            list: A 2D list representing the decoded solution. Each element is a tuple (color_index, direction_type).
                  color_index is the index of the assigned color for the cell.
                  direction_type is the direction type assigned to the cell (e.g., FlowFreeConstants.LR, FlowFreeConstants.TB, etc.), or -1 for endpoint cells (which do not have direction types).
        """

        sol = set(sol)  # Convert solution list to set for faster lookups (checking if a variable is in solution is faster in a set)
        num_colors = len(colors) # Get number of colors

        decoded = [] # Initialize list to store decoded puzzle grid (will be a 2D list of (color_index, direction_type) tuples)

        for i, row in enumerate(puzzle): # Iterate over rows in puzzle
            decoded_row = [] # Initialize list for decoded row

            for j, char in enumerate(row): # Iterate over cells in row

                # find which color variable for this cell is in the solution set
                cell_color = -1  # Initialize cell color index to -1 (meaning no color assigned yet)

                for color in range(num_colors): # Iterate through possible colors
                    if color_var(i, j, color) in sol:  # Check if the color variable for this cell and color is present in the SAT solution set (meaning it's true)
                        assert cell_color == -1  # Assert that only one color variable is true for each cell (one-hot encoding constraint). If cell_color is not -1, it means a color was already assigned, violating one-hot encoding.
                        cell_color = color  # Set the cell color index to the current color index

                assert cell_color != -1  # Ensure a color was assigned to each cell. After iterating through all colors, cell_color should have been set to a valid color index.

                cell_dir_type = -1 # Initialize direction type for cell to -1 (default value for endpoints or cells without direction type)

                if not char.isalnum():  # not a flow endpoint (need to determine direction type from SAT solution)

                    # find which direction type variable for this cell is in the solution set
                    for dir_type, dir_var in dir_vars[i, j].items(): # Iterate through direction types and their corresponding SAT variables for the current cell
                        if dir_var in sol:  # Check if a direction variable is present in the SAT solution set (meaning it's true)
                            assert cell_dir_type == -1  # Assert that only one direction variable is true for each non-endpoint cell (one-hot encoding for direction).
                            cell_dir_type = dir_type  # Set the direction type to the current direction type

                    assert cell_dir_type != -1  # Ensure a direction type was assigned for non-endpoint cells. After checking all direction types, cell_dir_type should have been set to a valid direction type.

                decoded_row.append((cell_color, cell_dir_type)) # Append tuple of (color_index, direction_type) to the decoded row for the current cell

            decoded.append(decoded_row)  # Append the decoded row to the decoded puzzle grid

        return decoded # Return the fully decoded puzzle grid as a 2D list

    @staticmethod
    def find_path(decoded, visited, cur_i, cur_j):
        """
        Follow a path starting from an arbitrary row, column location on the grid until a non-path cell is detected, or a cycle is found.
        Returns a list of (row, column) pairs on the path, as well as a boolean flag indicating if a cycle was detected.
        This method performs a depth-first search (DFS) to trace a path of a flow in the decoded solution.
        It starts from a given cell and follows the connections based on direction types until it reaches a dead end (no more connections in the direction) or detects a cycle (revisits a cell already on the current path).

        Args:
            decoded (list of list): The decoded puzzle solution grid (2D list of (color_index, direction_type) tuples).
            visited (list of list): A 2D grid of same size as puzzle, used to track visited cells during path traversal to detect cycles.
                                    Initialized to all 0s before calling find_path for a new path.
            cur_i (int): Starting row index for path tracing.
            cur_j (int): Starting column index for path tracing.

        Returns:
            tuple: A tuple containing:
                - run (list): List of (row_index, column_index) pairs representing the cells on the path found so far.
                - is_cycle (bool): True if a cycle was detected during path tracing, False otherwise.
        """

        size = len(decoded) # Get size of the decoded puzzle grid

        run = []  # Initialize list to store the path (sequence of cells as (row, column) tuples)
        is_cycle = False  # Flag to indicate if a cycle is detected during path tracing, initially set to False
        prev_i, prev_j = -1, -1  # Initialize previous cell coordinates to (-1, -1) to avoid immediately going back to the starting cell

        while True: # Loop to follow the path until a dead end or cycle is found

            advanced = False # Flag to check if the path was extended in the current iteration. Set to False at the beginning of each iteration.

            # get current cell's color and direction type, mark as visited, and add to the current path 'run'
            color, dir_type = decoded[cur_i][cur_j] # Get color and direction type of the current cell from the decoded grid
            visited[cur_i][cur_j] = 1  # Mark the current cell as visited in the 'visited' grid
            run.append((cur_i, cur_j))  # Add the current cell's coordinates (row, column) to the path 'run'

            # loop over valid neighbors of the current cell
            for dir_bit, n_i, n_j in SATHelper.get_valid_neighbors(size, cur_i, cur_j): # Iterate over valid neighbors of the current cell

                # do not consider prev pos (avoid immediately going back to the cell we just came from, preventing infinite loops)
                if (n_i, n_j) == (prev_i, prev_j):
                    continue # Skip this neighbor if it's the immediately previous cell in the path

                # get neighbor's color & dir type
                n_color, n_dir_type = decoded[n_i][n_j] # Get color and direction type of the neighbor cell

                # Check if these two cells are connected based on their direction types.
                # They are connected if either:
                # 1. The current cell's direction type includes the direction bit towards the neighbor (dir_type & dir_bit)
                # 2. The current cell is an endpoint (dir_type == -1) AND the neighbor's direction type includes the flipped direction bit back to the current cell (n_dir_type & FlowFreeConstants.DIR_FLIP[dir_bit]).
                if ((dir_type >= 0 and (dir_type & dir_bit)) or
                        (dir_type == -1 and n_dir_type >= 0 and
                         n_dir_type & FlowFreeConstants.DIR_FLIP[dir_bit])):

                    # if connected, they must have the same color. Assert this condition to verify solution correctness.
                    assert color == n_color

                    # detect cycle: if the neighbor is already visited in the current path traversal, it's a cycle
                    if visited[n_i][n_j]:
                        is_cycle = True # Set the cycle flag to True as a cycle is detected
                    else:
                        prev_i, prev_j = cur_i, cur_j # Update previous cell coordinates to the current cell before moving to the neighbor
                        cur_i, cur_j = n_i, n_j # Move to the neighbor cell for the next iteration of path tracing
                        advanced = True # Set the 'advanced' flag to True because the path has been extended

                    # either cycle detected or path advanced, so stop looking at other neighbors of the current cell in this iteration
                    break # Break out of the neighbor loop to proceed to the next cell in the path or terminate the path tracing

            # if path not advanced in this iteration (no new neighbor was found to extend the path), quit the path tracing loop (dead end or no more connections)
            if not advanced:
                break # Break out of the main path tracing loop

        return run, is_cycle # Return the traced path (list of cells) and the cycle detection status (boolean)

    @staticmethod
    def detect_cycles_in_solution(decoded, dir_vars):
        """
        Examine the decoded SAT solution to see if any cycles exist; if so,
        return the CNF clauses that need to be added to the problem in order to prevent them.
        This method scans the decoded solution to identify any cycles. If cycles are found, it generates CNF clauses
        that, when added to the SAT problem, will prevent these cycles from appearing in subsequent solutions.
        Cycles in Flow Free solutions are invalid because paths should only connect endpoints without looping back on themselves.

        Args:
            decoded (list of list): The decoded puzzle solution grid.
            dir_vars (dict): Dictionary of direction variables, needed to retrieve the SAT variables corresponding to direction types in cycle cells.

        Returns:
            list: A list of CNF clauses (lists of integers) to prevent cycles.
                  Each clause is a disjunction of negated direction variables that form a cycle.
                  Returns an empty list if no cycles are detected in the decoded solution.
        """

        size = len(decoded)  # Get size of decoded puzzle grid
        colors_seen = set() # Keep track of colors for which paths have already been checked for cycles. Used to avoid redundant path checks.
        visited = [[0] * size for _ in range(size)]  # Initialize a 2D visited grid to all 0s before each path traversal.
                                                    # Used by find_path to track visited cells during path tracing for cycle detection.

        # for each cell in the decoded puzzle
        for i, j, (color, dir_type) in SATHelper.explode_puzzle(decoded):

            # if flow endpoint for a color we haven't dealt with yet
            if dir_type == -1 and color not in colors_seen: # Check if the current cell is an endpoint and if we have not already processed paths for this color.
                                                            # We start path tracing from each endpoint to ensure all paths are checked.

                # add it to set of colors dealt with to avoid reprocessing paths of the same color
                assert not visited[i][j]  # Ensure the endpoint cell is not already visited. Endpoints should be starting points of new paths.
                colors_seen.add(color)  # Mark this color as processed, so we don't start another path trace from another endpoint of the same color.

                # mark the path as visited and check for cycle from this endpoint. Paths starting from endpoints should not form cycles in a valid solution.
                run, is_cycle = SolutionDecoder.find_path(decoded, visited, i, j) # Trace the path starting from this endpoint.
                assert not is_cycle # Assert that a path starting from an endpoint should not form a cycle. If it does, something is wrong with the solution.

        # see if there are any unvisited cells after processing all endpoint paths, if so they belong to cycles.
        # In a valid Flow Free solution, all cells that are part of a path should be reachable from an endpoint.
        # Unvisited cells after checking all paths from endpoints must be part of cycles.
        extra_clauses = [] # Initialize list to store clauses that prevent cycles. These clauses will be added to the SAT problem for the next iteration.

        for i, j in itertools.product(range(size), range(size)): # Iterate through all cells in the grid

            if not visited[i][j]:  # if unvisited cells remain, it indicates a cycle. Cells in valid paths would have been visited from endpoint path tracing.

                # get the path of the cycle by starting a path trace from this unvisited cell.
                run, is_cycle = SolutionDecoder.find_path(decoded, visited, i, j) # Trace the path starting from the unvisited cell.
                assert is_cycle # Assert that the path starting from an unvisited cell must be a cycle.

                # generate a clause negating the conjunction of all direction types along the cycle path.
                # This clause will prevent this specific cycle from appearing again in future SAT solutions.
                clause = [] # Initialize clause for cycle prevention

                for r_i, r_j in run: # For each cell (r_i, r_j) in the cycle path 'run'
                    _, dir_type = decoded[r_i][r_j] # Get the direction type of the cell in the cycle
                    if (r_i,r_j) in dir_vars and dir_type in dir_vars[(r_i,r_j)]: # Check if a direction variable exists for this cell and direction type.
                                                                                   # This condition should always be true for cells in a cycle from a valid solution.
                        dir_var = dir_vars[r_i, r_j][dir_type] # Get the SAT variable index for this direction type in this cell.
                        clause.append(-dir_var) # Negate the direction variable and add it to the clause.
                                                # Negating a direction variable in the clause means that this specific direction type in this specific cell cannot be true in future solutions, thus breaking the cycle.

                extra_clauses.append(clause)  # Add the generated clause to the list of extra clauses.
                                             # Each clause prevents one specific cycle. Multiple cycles might be found and multiple clauses generated in one iteration.

        # return whatever clauses we had to generate (could be empty list if no cycles were detected)
        return extra_clauses # Return the list of clauses designed to prevent cycles. If no cycles were found, this list will be empty.


# Class for solving SAT problems
class SATSolver:
    """
    Solves Flow Free puzzles using SAT (Satisfiability).
    This class encapsulates the iterative SAT solving process for Flow Free.
    It takes the SAT clauses generated by SATClauseGenerator, solves them using a SAT solver (pycosat), decodes the solution using SolutionDecoder, and checks for cycles using SolutionDecoder.
    If cycles are found, it generates clauses to prevent them and repeats the solving process until a cycle-free solution is found or it's determined that no solution exists.
    This iterative approach is necessary because initial SAT solving might produce solutions with cycles, which are invalid in Flow Free.
    """

    @staticmethod
    def solve_flow_free_sat(options, puzzle, colors, color_var, dir_vars, clauses, cell_size):
        """
        Solve the SAT problem now that it has been reduced to a list of clauses in CNF.
        This is an iterative process: first we try to solve a SAT problem with the current set of clauses, then we detect cycles in the solution.
        If cycles are found, clauses are generated to prevent them from recurring in subsequent solutions, and the next iteration of solving begins with the updated set of clauses.
        This process repeats until a cycle-free solution is found or the SAT solver determines that the problem is unsatisfiable (no solution exists).

        Args:
            options (argparse.Namespace): Command-line options (not heavily used in GUI, but included for potential future use).
            puzzle (list of str): The parsed puzzle grid.
            colors (dict): Dictionary of color mnemonics to color indices.
            color_var (function): Function to get color variable index.
            dir_vars (dict): Dictionary of direction variables.
            clauses (list): List of CNF clauses representing the Flow Free puzzle constraints.
            cell_size (int): Size of each cell in pixels (for GUI display, not directly used in the SAT solving logic itself).

        Returns:
            tuple: A tuple containing:
                - sol (list or str): SAT solution set (list of true variables) if a solution is found. Returns 'UNSAT' if the problem is unsatisfiable, or 'UNKNOWN' if the solver's result is indeterminate.
                - decoded (list of list): Decoded puzzle solution grid (2D list of (color_index, direction_type) tuples) if a solution is found, None if no solution exists.
                - repairs (int): Number of cycle repairs performed during the solving process. Counts how many times cycles were detected and clauses were added to prevent them.
                - solve_time (float): Total time taken for the solving process, including all iterations and cycle repairs, in seconds.
            tuple: (None, None, 0, 0) if an error occurred during SAT solving, for example, if pycosat raises an exception. In this case, an error message is shown to the user.
        """

        start = datetime.now()  # Record the start time of the entire solving process

        decoded = None  # Initialize decoded solution variable to None, will be set if a valid solution is found
        all_decoded = [] # List to store all decoded solutions obtained in each iteration, including intermediate solutions with cycles. Used for debugging and cycle visualization.
        repairs = 0  # Initialize counter for cycle repairs to 0

        try:
            while True: # Start of the iterative solving loop. This loop continues until a cycle-free solution is found or no solution exists.
                sol = pycosat.solve(clauses)  # pylint: disable=E1101 # Solve the current set of SAT clauses using pycosat solver.
                                                # pycosat.solve returns a list of true variable indices if satisfiable, 'UNSAT' if unsatisfiable, or 'UNKNOWN' if the result is indeterminate.

                if not isinstance(sol, list):  # Check if the solver returned a solution (list of variables) or an indication of no solution ('UNSAT' or 'UNKNOWN').
                    decoded = None # If solver did not return a list, it means no solution was found or result is unknown. Set decoded solution to None.
                    all_decoded.append(decoded) # Append None to all_decoded list to record that no solution was found in this iteration.
                    break # Exit the solving loop as no solution was found.

                decoded = SolutionDecoder.decode_sat_solution(puzzle, colors, color_var, dir_vars, sol)  # Decode the SAT solution (list of variables) back into a Flow Free puzzle grid format.
                all_decoded.append(decoded) # Append the decoded solution (which might contain cycles) to the list of all decoded solutions.

                extra_clauses = SolutionDecoder.detect_cycles_in_solution(decoded, dir_vars)  # Detect cycles in the decoded solution.
                                                                                              # Returns a list of clauses to prevent the detected cycles, or an empty list if no cycles are found.

                if not extra_clauses:  # Check if any cycle-preventing clauses were returned. An empty list means no cycles were detected.
                    break # If no cycles were found, it means a valid cycle-free solution is obtained. Exit the solving loop.

                clauses += extra_clauses  # If cycles were found, add the cycle-preventing clauses to the current set of SAT clauses.
                                         # These new clauses will constrain the solution space in the next iteration to avoid the detected cycles.
                repairs += 1 # Increment the cycle repair count, indicating that a cycle was detected and clauses were added to fix it.

            solve_time = (datetime.now() - start).total_seconds() # Calculate the total time taken for the entire solving process, from start to finding a solution or determining no solution.

            if not options.quiet: # If not in quiet mode (usually for command-line, but GUI sets quiet=True), print solving statistics and solution (or lack thereof) to console.
                if options.display_cycles: # Check if the 'display_cycles' option is enabled (usually for debugging purposes).
                    for cycle_decoded in all_decoded[:-1]: # Iterate through all intermediate decoded solutions (excluding the final one, which might be None or a valid solution).
                        print('intermediate solution with cycles:') # Print a message indicating an intermediate solution with cycles.
                        GridDrawer.draw_grid_solution(puzzle, colors, cycle_decoded, cell_size) # Draw the intermediate solution with cycles on the console (text-based grid representation).

                if decoded is None: # Check if a valid decoded solution was found (decoded is None if no solution or UNSAT).
                    print(f'solver returned {str(sol)} after {repairs:,} cycle ' # Print a message indicating that no solution was found and the solver's result.
                        f'repairs and {solve_time:.3f} seconds') # Include the number of cycle repairs and the total solving time.

                else: # If a valid decoded solution was found (decoded is not None).
                    print(
                        f'obtained solution after {repairs:,} cycle repairs and {solve_time:.3f} seconds:') # Print a success message with the number of cycle repairs and total solving time.
                    print()
                    GridDrawer.draw_grid_solution(puzzle, colors, decoded, cell_size)  # Draw the final solved grid on the console (text-based grid representation).

            return sol, decoded, repairs, solve_time # Return the SAT solver's result (sol), the decoded puzzle solution (decoded), the number of cycle repairs (repairs), and the total solving time (solve_time).

        except pycosat.Error as e:  # Catch specific pycosat errors, like solver-related issues (e.g., solver not found, solver crashed).
            messagebox.showerror("Error", f"An error occurred during SAT solving: {e}") # Show an error message box to the user indicating a SAT solver error.
            return None, None, 0, 0 # Return error indicators: None for solution and decoded solution, 0 for repairs and solve time.

        except Exception as e: # Catch any other unexpected exceptions that might occur during the solving process (e.g., programming errors, unexpected library behavior).
            messagebox.showerror("Error", f"An unexpected error occurred: {e}") # Show an error message box to the user indicating an unexpected error.
            return None, None, 0, 0 # Return error indicators: None for solution and decoded solution, 0 for repairs and solve time.


# Class for drawing the grid on the GUI
class GridDrawer:
    """
    Draws the Flow Free grid and solution lines on the Tkinter canvas.
    This class is responsible for rendering the Flow Free grid, including the grid lines and the solution paths, on a Tkinter Canvas widget.
    It uses the decoded solution from the SAT solver to draw colored lines representing the flow paths between endpoints.
    The drawing includes grid lines, colored lines for paths, and potentially highlights for endpoints.
    """

    @staticmethod
    def draw_grid_solution(puzzle, colors, decoded_solution, cell_size, canvas, line_size):
        """
        Draws the grid solution on the canvas.
        Renders the Flow Free grid and the solution paths as colored lines on the provided Tkinter Canvas.
        It iterates through the decoded solution grid and draws lines based on the direction type of each cell to visually represent the flow paths.
        The lines are colored according to the color assigned to each path.

        Args:
            puzzle (list of str): The parsed puzzle grid (used for size and to identify endpoint cells).
            colors (dict): Dictionary of color mnemonics to color indices, used to map color indices back to mnemonics for color names.
            decoded_solution (list of list): The decoded puzzle solution grid (2D list of (color_index, direction_type) tuples).
            cell_size (int): Size of each cell in pixels, determines the dimensions of the grid cells on the canvas.
            canvas (tk.Canvas): Tkinter Canvas widget on which to draw the grid and solution lines.
            line_size (int): Thickness of the solution lines to be drawn on the canvas.
        """
        if not canvas: # Check if the canvas object is valid (not None). If canvas is None, drawing is not possible, so return.
            return

        # Delete existing lines are handled in apply_line_size method of FlowFreeGUI. Ensure that when line size is changed, old lines are cleared before drawing new ones.
        # (Note: the actual deletion of lines is done in the GUI class, not here, as indicated in the original comment. This method just draws, it doesn't manage existing drawings).
        size = len(puzzle) # Get puzzle size from the puzzle grid
        color_mnemonics_for_grid = [None] * len(colors) # Initialize a list to map color indices back to color mnemonics. Size is based on the number of colors.
        for char, color_index in colors.items(): # Iterate through the colors dictionary (mnemonic to index mapping).
            color_mnemonics_for_grid[color_index] = char # Populate the list so that color_mnemonics_for_grid[color_index] gives the mnemonic for that color index.

        for row_index, row in enumerate(puzzle): # Iterate through each row of the puzzle grid
            for col_index, char in enumerate(row): # Iterate through each cell in the current row
                x1, y1 = col_index * cell_size, row_index * cell_size # Calculate the top-left corner coordinates (x1, y1) of the current cell on the canvas.
                x2, y2 = x1 + cell_size, y1 + cell_size # Calculate the bottom-right corner coordinates (x2, y2) of the current cell.

                color_index, direction_type = decoded_solution[row_index][col_index] # Get the color index and direction type for the current cell from the decoded solution.
                color_mnemonic = color_mnemonics_for_grid[color_index] # Get the color mnemonic (e.g., 'R', 'B') corresponding to the color index.
                line_color_name = FlowFreeConstants.COLOR_NAMES.get(color_mnemonic, 'black') # Get the full color name (e.g., 'Red', 'Blue') from the mnemonic using COLOR_NAMES dictionary.
                                                                                              # If the mnemonic is not found, default to 'black'.

                if not char.isalnum(): # Check if the current cell is not an endpoint (i.e., it's a cell that is part of a flow path, represented by '.' in the puzzle input).
                                      # Endpoint cells are marked with alphanumeric characters (color labels) in the puzzle.
                    if direction_type != -1: # Check if a direction type is assigned to this cell (direction_type is -1 for endpoint cells).
                                            # If direction_type is not -1, it means this cell is part of a path and has a direction.
                        line_color = line_color_name  # Get the color name for drawing the line, derived from the color mnemonic.
                        line_width = line_size  # Get the line thickness from the input line_size parameter.

                        center_x = int((x1 + x2) / 2)  # Calculate the horizontal center coordinate of the cell.
                        center_y = int((y1 + y2) / 2) # Calculate the vertical center coordinate of the cell.

                        # Draw lines based on direction_type, with a black outline for better visibility.
                        # For each direction type (LR, TB, TL, TR, BL, BR), draw lines on the canvas.
                        # Each line is drawn with a slightly thicker black outline first, then with the actual color line on top, creating a border effect.
                        if direction_type == FlowFreeConstants.LR: # Left-Right direction
                             # Black outline (slightly thicker)
                            canvas.create_line(x1, center_y, x2, center_y, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                             # Actual color line (thinner than outline)
                            canvas.create_line(x1, center_y, x2, center_y, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                        elif direction_type == FlowFreeConstants.TB: # Top-Bottom direction
                            # Black outline (slightly thicker)
                            canvas.create_line(center_x, y1, center_x, y2, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                            # Actual color line (thinner than outline)
                            canvas.create_line(center_x, y1, center_x, y2, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                        elif direction_type == FlowFreeConstants.TL: # Top-Left direction
                            # Black outline (slightly thicker)
                            canvas.create_line(x1, center_y, center_x, center_y, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y1, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                             # Actual color line (thinner than outline)
                            canvas.create_line(x1, center_y, center_x, center_y, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y1, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                        elif direction_type == FlowFreeConstants.TR: # Top-Right direction
                             # Black outline (slightly thicker)
                            canvas.create_line(center_x, center_y, x2, center_y, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y1, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                             # Actual color line (thinner than outline)
                            canvas.create_line(center_x, center_y, x2, center_y, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y1, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                        elif direction_type == FlowFreeConstants.BL: # Bottom-Left direction
                            # Black outline (slightly thicker)
                            canvas.create_line(x1, center_y, center_x, center_y, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y2, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                             # Actual color line (thinner than outline)
                            canvas.create_line(x1, center_y, center_x, center_y, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y2, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                        elif direction_type == FlowFreeConstants.BR: # Bottom-Right direction
                             # Black outline (slightly thicker)
                            canvas.create_line(center_x, center_y, x2, center_y, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y2, width=line_width + 2, fill="black", tags="path", joinstyle="round", capstyle="round")
                             # Actual color line (thinner than outline)
                            canvas.create_line(center_x, center_y, x2, center_y, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")
                            canvas.create_line(center_x, center_y, center_x, y2, width=line_width, fill=line_color, tags="path", joinstyle="round", capstyle="round")


# Main GUI class
class FlowFreeGUI:
    """
    Main GUI class for the Flow Free solver application.
    This class sets up and manages the graphical user interface for the Flow Free solver.
    It handles user interactions, puzzle input through a grid interface, initiates the solving process, and displays the solution on the canvas.
    It uses Tkinter to create the GUI elements and integrates with the SAT solver backend to solve Flow Free puzzles.
    """

    def __init__(self):
        """
        Initializes the GUI window, canvas, and other UI elements.
        Sets up the main window (Tk root), title, default options (using argparse, though mostly for internal settings), canvas for drawing, color palettes for user interaction,
        and binds event handlers for user actions. Also initializes internal state variables like cell colors, grid size, and solution.
        """
        self.root = Tk() # Create the main Tkinter window.
        self.root.title("Flow Free Solver GUI") # Set the title of the main window.
        self.options = ArgumentParser().parse_args() # Initialize command-line options using argparse (though not heavily used in GUI).
        self.options.quiet = True # Set 'quiet' option to True to suppress console output during SAT solving (suitable for GUI).
        self.options.display_cycles = False # Set 'display_cycles' option to False to disable display of intermediate solutions with cycles by default (can be toggled for debugging).
        self.canvas = None # Initialize canvas to None; it will be created later when the grid is created.
        self.cell_colors = {} # Dictionary to store the color of each cell in the grid, used for user input and puzzle definition. Keys are (row, column) tuples, values are color names or None.
        self.colors = {} # Dictionary to store color information extracted from the puzzle, mapping mnemonics to color indices. Populated during puzzle parsing.
        self.color_chars = [] # List of color mnemonic characters, used for indexing and mapping colors.
        self.selected_color = None # Stores the currently selected color from the color palette, used when setting cell colors in the grid.
        self.grid_size_value = 0 # Stores the size of the grid (width and height, assuming square grid), set by user input.
        self.cell_size = 60 # Default size of each cell in pixels on the canvas.
        self.line_size = 10 # Default thickness of the solution lines drawn on the canvas.
        self.decoded_solution = None # Stores the decoded solution grid (2D list) after solving, initially None until a solution is found.
        self.color_palette_frame = None # Tkinter Frame to hold the color palette buttons, initialized to None and created in _create_grid_ui.
        self.canvas_frame = None # Tkinter Frame to hold the canvas widget, initialized to None and created in _create_grid_ui.
        self.options_frame = None # Tkinter Frame for general options (currently not heavily used), initialized to None and created if needed.
        self.line_size_entry = None # Tkinter Entry widget for user to input line size, initialized to None and created in _create_grid_ui.
        self.cell_size_entry = None # Tkinter Entry widget for user to input cell size, initialized to None and created in _create_grid_ui.

        self._setup_ui() # Call the _setup_ui method to initialize and set up the user interface.

    def apply_line_size(self):
         """
         Applies the line size entered by the user and refreshes the grid drawing.
         Gets the line size value from the line size entry widget, validates it to ensure it's within a reasonable range (1 to max allowed line size for current cell size),
         and then redraws the solution lines on the canvas with the new line size if a solution is already displayed.
         If no solution is displayed, it just refreshes the grid to clear any previous drawings, preparing for a new solution or puzzle input.
         """
         try:
             self.line_size = int(self.line_size_entry.get()) # Get the line size value from the Entry widget and convert it to an integer.
             max_line_size = int(self.cell_size * 2 / 3) # Calculate the maximum allowed line size based on the current cell size (e.g., 2/3 of cell size).
             if not (1 <= self.line_size <= max_line_size): # Validate if the entered line size is within the valid range (between 1 and max_line_size).
                 messagebox.showerror("Error", f"Line size must be between 1 and {max_line_size}.") # Show error message if line size is out of range.
                 return # Exit the method if line size is invalid.
             if self.decoded_solution: # Check if a solution is already decoded and displayed.
                 self.canvas.delete("path") # If a solution is displayed, delete all existing path lines from the canvas before redrawing.
                 self._draw_solution_lines() # Redraw the solution lines with the new line size.
             else:
                 self._refresh_grid() # If no solution is displayed, just refresh the grid (e.g., to clear any previous drawings).
         except ValueError:
             messagebox.showerror("Error", "Invalid line size. Please enter numbers.") # Show error message if the entered line size is not a valid integer.

    def _calculate_canvas_size(self):
        """
        Calculates the canvas size based on the current grid size and cell size.
        Returns the total size (width and height, as canvas is square) of the canvas required to display the grid.
        Canvas size is grid size (number of cells in a row/column) multiplied by cell size (pixels per cell).

        Returns:
            int: The calculated canvas size in pixels.
        """
        return self.grid_size_value * self.cell_size # Calculate and return the canvas size (width = height = grid_size * cell_size).

    def _draw_solution_lines(self):
        """
        Draws the solution lines on the canvas based on the current decoded solution.
        Generates a puzzle string from the current grid state (cell colors), parses it to get puzzle and color information,
        and then calls GridDrawer.draw_grid_solution to render the solution lines on the canvas.
        This method is called after a solution is found or when line size is changed to redraw the solution lines.
        """
        puzzle_string = self._generate_puzzle_string() # Generate a puzzle string representation from the current grid state.
        puzzle, colors = PuzzleParser.parse_puzzle(self.options, puzzle_string, filename='GUI Input') # Parse the generated puzzle string to get puzzle grid and color information.
        if puzzle and colors: # Check if parsing was successful (puzzle and colors are not None).
            GridDrawer.draw_grid_solution(puzzle, colors, self.decoded_solution, self.cell_size, self.canvas, self.line_size) # Call GridDrawer to draw the solution lines on the canvas.

    def _setup_ui(self):
        """
        Sets up the main user interface elements.
        This method is called during GUI initialization to create and arrange the UI elements in the main window.
        Currently, it only calls _create_input_frame to set up the initial input frame for grid dimensions.
        More UI elements can be added here or in separate methods called from here.
        """
        self._create_input_frame() # Call _create_input_frame to create the input frame for grid size.
        self.root.mainloop() # Start the Tkinter main event loop, which listens for events and updates the GUI.

    def _create_input_frame(self):
        """
        Creates the input frame at the top of the GUI for entering grid dimensions and creating the grid.
        This frame contains a single entry widget for grid size and a button to create the grid based on entered dimensions.
        It uses ttk.Frame and ttk.LabelFrame for styled frames and labels, and Button for the 'Create Grid' button.
        """
        input_frame = ttk.Frame(self.root) # Create a styled frame (ttk.Frame) to contain input widgets.
        input_frame.pack(pady=10) # Pack the input frame at the top of the root window with vertical padding.

        top_frame = ttk.Frame(input_frame) # Create another styled frame within the input frame.
        top_frame.pack(side=tk.TOP, pady=5) # Pack this frame at the top of the input frame with vertical padding.

        grid_size_frame = ttk.LabelFrame(top_frame, text="Grid Size") # Create a styled labeled frame (ttk.LabelFrame) for grid size inputs, with "Grid Size" as label.
        grid_size_frame.pack(side=tk.LEFT, padx=10) # Pack this labeled frame to the left with horizontal padding.

        ttk.Label(grid_size_frame, text="Grid Size:").grid(row=0, column=0, sticky="w", padx=5, pady=5) # Create a styled label for "Grid Size:" and place it in the grid layout.
        self.size_entry = ttk.Entry(grid_size_frame, width=5) # Create a styled entry widget (ttk.Entry) for entering grid size, with width set to 5 characters.
        self.size_entry.insert(0, "5") # Insert default value "5" into the size entry widget.
        self.size_entry.grid(row=0, column=1, sticky="ew", padx=5, pady=5) # Place the size entry widget in the grid layout, stretching horizontally.

        create_button = Button(grid_size_frame, text="Create Grid", command=self._create_grid_ui) # Create a standard Tkinter Button with text "Create Grid" and command to call _create_grid_ui method when clicked.
        create_button.grid(row=0, column=2, sticky="ew", padx=10, pady=5) # Place the create button in the grid layout, stretching horizontally.

        self.top_frame = top_frame # Store the top frame in self.top_frame for potential future use or reference.

    def _process_puzzle_command(self):
        """
        Processes the command to solve the puzzle.
        This method is triggered when the "Solve Puzzle" button is clicked. It performs the following steps:
        1. Checks if the canvas and grid size are initialized; shows error if not.
        2. Generates a puzzle string from the current state of the GUI grid (cell colors).
        3. Collects endpoint colors set by the user on the grid.
        4. Validates if all specified colors have both start and end points; shows error if not.
        5. Parses the puzzle string using PuzzleParser.
        6. Reduces the puzzle to a SAT problem using SATClauseGenerator.
        7. Solves the SAT problem using SATSolver.
        8. If a solution is found, decodes it and draws the solution lines on the canvas.
        9. If no solution is found, informs the user via a message box.
        """
        if not self.canvas: # Check if the canvas widget is created.
            messagebox.showerror("Error", "Please create a grid first.") # Show error if canvas is not created.
            return # Exit the method if canvas is not available.
        if not self.grid_size_value: # Check if grid size has been set.
            messagebox.showerror("Error", "Please specify grid dimensions and create a grid.") # Show error if grid size is not set.
            return # Exit if grid size is not set.

        puzzle_string = self._generate_puzzle_string() # Generate a puzzle string from the current state of the GUI grid.

        endpoint_colors_set = set() # Initialize a set to store unique endpoint colors set by the user.
        for (row_index, col_index), color_name in self.cell_colors.items(): # Iterate through all cells and their assigned colors in self.cell_colors dictionary.
            if color_name: # If a color is assigned to the cell (i.e., it's an endpoint).
                endpoint_colors_set.add(color_name) # Add the color name to the set of endpoint colors.

        endpoint_mnemonics = [ # Generate a list of mnemonics for the endpoint colors.
            list(FlowFreeConstants.COLOR_NAMES.keys())[ # For each color name in endpoint_colors_set, find its mnemonic.
                list(FlowFreeConstants.COLOR_NAMES.values()).index(color_name)] for color_name in # Iterate through endpoint_colors_set.
            endpoint_colors_set] # List comprehension to create a list of mnemonics.

        if len(endpoint_colors_set) < len(endpoint_mnemonics): # Check if the number of unique endpoint colors is less than the number of mnemonics (this check might be redundant as they should be the same).
            missing_colors = [color_name for color_name in FlowFreeConstants.COLOR_NAMES.values() # Find color names that are in COLOR_NAMES values but not in endpoint_colors_set, and are associated with endpoint mnemonics.
                              if color_name not in endpoint_colors_set and color_name in [ # Filter color names.
                                  FlowFreeConstants.COLOR_NAMES.get(mnemonic) for mnemonic in # Get color names corresponding to endpoint mnemonics.
                                  endpoint_mnemonics]] # List comprehension to get color names related to mnemonics.
            if missing_colors: # Check if there are any missing colors (this part of the logic needs review as it seems to be checking for something that should not happen).
                messagebox.showerror("Error",
                                     f"The following colors are missing start or end points: {', '.join(missing_colors)}") # Show error message about missing start or end points (this message is likely incorrect for the current logic).
                return # Exit if there are "missing" colors (according to the potentially flawed logic).

        options = ArgumentParser().parse_args() # Initialize command-line options (though not heavily used in GUI).
        options.quiet = True # Set 'quiet' option to True for GUI mode.

        puzzle, colors = PuzzleParser.parse_puzzle(options, puzzle_string, filename='GUI Input') # Parse the puzzle string using PuzzleParser to get puzzle and color information.
        if puzzle is None: # Check if puzzle parsing failed (parse_puzzle returns None if there's an error).
            return # Exit if puzzle parsing failed.

        color_var_func, direction_vars, num_vars, clauses, reduction_time = SATClauseGenerator.reduce_puzzle_to_sat( # Reduce the parsed puzzle to a SAT problem by generating SAT clauses.
            options, puzzle, colors) # Call SATClauseGenerator.reduce_puzzle_to_sat to get color variable function, direction variables, number of variables, clauses, and reduction time.

        if color_var_func is None: # Check if SAT reduction failed (reduce_puzzle_to_sat returns None if there's an error).
            return # Exit if SAT reduction failed.

        sat_solution, decoded_solution, cycle_repair_count, solve_time = SATSolver.solve_flow_free_sat(options, # Solve the SAT problem using SATSolver.solve_flow_free_sat.
                                                                                                   puzzle, colors, # Pass options, puzzle, colors,
                                                                                                   color_var_func, # color variable function,
                                                                                                   direction_vars, # direction variables,
                                                                                                   clauses, # clauses,
                                                                                                   self.cell_size) # and cell size to the solver.

        if decoded_solution: # Check if a decoded solution was returned (meaning SAT solver found a solution).
            self.decoded_solution = decoded_solution # Store the decoded solution in self.decoded_solution.
            self._draw_solution_lines() # Draw the solution lines on the canvas using _draw_solution_lines method.
        elif sat_solution is not None: # Check if SAT solver returned a result (even if it's not a solution, e.g., UNSAT).
            messagebox.showinfo("Info", "No solution exists for this puzzle.") # If sat_solution is not None but decoded_solution is None, it means no solution exists. Show info message.


    def apply_cell_size(self):
        """Applies the cell size and refreshes the grid, adjusting line size if necessary."""
        try:
            new_cell_size = int(self.cell_size_entry.get()) # Get the new cell size from the entry and convert to integer.
            if not (10 <= new_cell_size <= 100): # Validate if the new cell size is within the allowed range (10 to 100 pixels).
                messagebox.showerror("Error", "Cell size must be between 10 and 100.") # Show error if cell size is out of range.
                return # Exit if cell size is invalid.

            max_line_size_new = int(new_cell_size * 2 / 3) # Calculate the maximum allowed line size for the new cell size.

            if self.line_size > max_line_size_new: # Check if the current line size is greater than the max allowed for the new cell size.
                self.line_size = max(1, max_line_size_new) # If current line size is too large, reduce it to the maximum allowed, but at least 1.
                self.line_size_entry.delete(0, tk.END) # Clear the line size entry.
                self.line_size_entry.insert(0, str(self.line_size)) # Insert the adjusted line size back into the entry.
                messagebox.showinfo("Info", f"Line size adjusted to {self.line_size} to be within valid range for new cell size.") # Inform user that line size was adjusted.


            self.cell_size = new_cell_size # Update the cell size to the new value.
            self._refresh_grid() # Refresh the grid to redraw it with the new cell size.
        except ValueError:
            messagebox.showerror("Error", "Invalid cell size. Please enter numbers.") # Show error if the entered cell size is not a valid number.

    def _create_grid_ui(self):
        """
        Creates the grid UI elements including canvas, color palette, and solve button.
        This method is called when the "Create Grid" button is clicked. It destroys any existing grid UI elements,
        reads grid dimensions from input entries, validates them, creates frames for canvas and color palette,
        creates the canvas for drawing the grid, and sets up the color palette with color selection buttons.
        It also sets up the "Solve Puzzle" button and initializes data structures for cell colors and color mnemonics.
        """
        if self.color_palette_frame: # Check if color palette frame already exists.
            self.color_palette_frame.destroy() # If yes, destroy it to create a new one.
        if self.canvas_frame: # Check if canvas frame already exists.
            self.canvas_frame.destroy() # If yes, destroy it.
        if self.options_frame: # Check if options frame exists (currently not used in provided code, but for future options).
            self.options_frame.destroy() # If yes, destroy it.

        if hasattr(self, 'main_frame') and self.main_frame: # Check if main frame exists.
            self.main_frame.destroy() # If yes, destroy it to start fresh.

        try:
            grid_size = int(self.size_entry.get()) # Get grid size from the size entry and convert to integer.
            if not (1 <= grid_size <= 20): # Validate if grid dimension is within allowed range (1 to 20).
                messagebox.showerror("Error", "Grid dimensions must be between 1 and 20.") # Show error if dimensions are out of range.
                return # Exit if dimensions are invalid.
            self.grid_size_value = grid_size # Set grid size value.
        except ValueError:
            messagebox.showerror("Error", "Invalid grid dimensions. Please enter numbers.") # Show error if entered dimensions are not valid numbers.
            return # Exit if dimensions are invalid.

        self.main_frame = Frame(self.root) # Create a main frame to hold all grid UI elements.
        self.main_frame.pack(fill=tk.BOTH, expand=True) # Pack the main frame to fill available space and expand.

        self.top_frame.grid(row=0, column=0, columnspan=2, sticky="ew", padx=5, pady=5) # Place the top frame (containing grid size inputs) in the main frame using grid layout.

        size_options_frame = ttk.LabelFrame(self.main_frame, text="Size Options") # Create a styled labeled frame for size options.
        size_options_frame.grid(row=1, column=0, sticky="ew", padx=10, pady=10) # Place size options frame in grid layout.

        Label(size_options_frame, text="Cell Size:").grid(row=0, column=0, sticky="w", padx=5, pady=5) # Label for cell size.
        self.cell_size_entry = Entry(size_options_frame, width=5) # Entry for cell size input.
        self.cell_size_entry.insert(0, str(self.cell_size)) # Set default cell size in entry.
        self.cell_size_entry.grid(row=0, column=1, sticky="w", padx=5, pady=5) # Place cell size entry in grid layout.


        apply_cell_size_button = Button(size_options_frame, text="Apply Cell Size", command=self.apply_cell_size) # Button to apply cell size.
        apply_cell_size_button.grid(row=0, column=2, sticky="w", padx=5, pady=5) # Place cell size apply button.

        Label(size_options_frame, text="Line Size:").grid(row=1, column=0, sticky="w", padx=5, pady=5) # Label for line size.
        self.line_size_entry = Entry(size_options_frame, width=5) # Entry for line size input.
        self.line_size_entry.insert(0, str(self.line_size)) # Set default line size in entry.
        self.line_size_entry.grid(row=1, column=1, sticky="w", padx=5, pady=5) # Place line size entry.

        apply_line_size_button = Button(size_options_frame, text="Apply Line Size", command=self.apply_line_size) # Button to apply line size.
        apply_line_size_button.grid(row=1, column=2, sticky="w", padx=5, pady=5) # Place line size apply button.

        solve_canvas_frame = ttk.LabelFrame(self.main_frame, text="Display") # Labeled frame for solve button and canvas.
        solve_canvas_frame.grid(row=1, column=1, rowspan=3, sticky="nsew", padx=10, pady=10) # Place solve/canvas frame.

        solve_button_frame = Frame(solve_canvas_frame) # Frame to hold solve button.
        solve_button_frame.grid(row=0, column=0, sticky="ew", padx=5, pady=5) # Place solve button frame.

        solve_button = Button(solve_button_frame, text="Solve Puzzle", command=self._process_puzzle_command) # Solve puzzle button.
        solve_button.pack(expand=True, fill=tk.BOTH) # Pack solve button to fill space.

        self.canvas_frame = Frame(solve_canvas_frame) # Frame to hold canvas.
        self.canvas_frame.grid(row=1, column=0, sticky="nsew", padx=5, pady=5) # Place canvas frame.

        canvas_size = self._calculate_canvas_size() # Calculate canvas size based on grid and cell size.
        self.canvas = Canvas(self.canvas_frame, width=canvas_size, height=canvas_size, bg="white") # Create canvas widget.
        self.canvas.pack(fill=tk.BOTH, expand=True) # Pack canvas to fill space.

        color_options_frame = ttk.LabelFrame(self.main_frame, text="Color Options") # Labeled frame for color options.
        color_options_frame.grid(row=3, column=0, sticky="nsew", padx=10, pady=10) # Place color options frame.

        self.color_palette_frame = Frame(color_options_frame) # Frame to hold color palette.
        self.color_palette_frame.grid(row=0, column=0, sticky="nsew", padx=10, pady=10) # Place color palette frame.

        self.selected_color = None # Initialize selected color to None.

        def set_color_command(color_name): # Define command for color buttons to set selected color.
            self.selected_color = color_name # Set selected color to the clicked color name.
            color_display_label.config(text=f"Selected Color: {color_name}") # Update label to show selected color.

        for i, color_name in enumerate(FlowFreeConstants.COLOR_NAMES.values()): # Iterate through color names from constants.
            color_label = Label(self.color_palette_frame, text=color_name, width=10, anchor="w") # Create label for color name.
            color_label.grid(row=i % 8, column=(i // 8) * 2, sticky="w") # Place color label in grid.

            color_button = Button(self.color_palette_frame, bg=color_name, width=2, # Create color button with background color set to color name.
                                    command=lambda c=color_name: set_color_command(c)) # Command to set selected color when button is clicked.
            color_button.grid(row=i % 8, column=(i // 8) * 2 + 1, pady=2, padx=2) # Place color button in grid.

        color_display_label = Label(color_options_frame, text="Select a color: ", fg="black") # Label to display selected color.
        color_display_label.grid(row=1, column=0, sticky="nsew", padx=10, pady=10) # Place color display label.

        self.cell_colors = {} # Initialize cell colors dictionary.
        self.colors = {} # Initialize colors dictionary.
        self.color_chars = [None] * len(FlowFreeConstants.COLOR_MNEMONICS) # Initialize color chars list.
        for i, mnemonic in enumerate(FlowFreeConstants.COLOR_MNEMONICS): # Iterate through color mnemonics.
            self.color_chars[i] = mnemonic # Populate color chars list with mnemonics.

        self.main_frame.grid_rowconfigure(3, weight=1) # Configure row 3 of main frame to expand vertically.
        self.main_frame.grid_columnconfigure(1, weight=1) # Configure column 1 of main frame to expand horizontally.

        self._refresh_grid() # Refresh the grid to draw initial grid lines and handle initial state.

    def _refresh_grid(self):
        """
        Refreshes the grid canvas, redrawing grid lines and endpoints based on current settings.
        This method is called to update the visual representation of the grid, e.g., after changing cell size or when initializing the grid.
        It clears the canvas, redraws grid lines, and re-renders endpoint circles based on the stored cell colors in self.cell_colors.
        It also sets up the event binding for mouse clicks on the canvas to handle user interaction for setting endpoints.
        """
        if not self.canvas: # Check if canvas exists.
            return # Exit if canvas is not created yet.

        saved_cell_colors = self.cell_colors.copy() # Create a copy of current cell colors to restore them after clearing.

        canvas_size = self._calculate_canvas_size() # Calculate new canvas size based on current grid and cell size.
        self.canvas.config(width=canvas_size, height=canvas_size) # Configure canvas widget with new size.
        self.canvas.delete("all") # Clear all drawings from the canvas.
        self.cell_colors = {} # Reset cell colors dictionary to start with a clean grid.

        for row_index in range(self.grid_size_value): # Iterate through rows of the grid.
            for col_index in range(self.grid_size_value): # Iterate through columns of the grid.
                x1, y1 = col_index * self.cell_size, row_index * self.cell_size # Calculate top-left corner coordinates of the cell.
                x2, y2 = x1 + self.cell_size, y1 + self.cell_size # Calculate bottom-right corner coordinates of the cell.
                self.canvas.create_rectangle(x1, y1, x2, y2, fill='white', outline="gray") # Draw a rectangle for each cell, filled white with gray outline.
                self.cell_colors[(row_index, col_index)] = None # Initialize cell color to None in cell_colors dictionary.

        def draw_endpoint_circle(row_index, col_index, color_name): # Define a local function to draw endpoint circles.
            x1, y1 = col_index * self.cell_size, row_index * self.cell_size # Calculate top-left corner.
            x2, y2 = x1 + self.cell_size, y1 + self.cell_size # Calculate bottom-right corner.
            center_x = (x1 + x2) / 2 # Calculate center x.
            center_y = (y1 + y2) / 2 # Calculate center y.
            radius = min(self.cell_size, self.cell_size) / 3 # Calculate radius of the circle, based on cell size.
            self.canvas.create_oval(center_x - radius, center_y - radius, center_x + radius, center_y + radius, fill=color_name, tags=f"endpoint_{row_index}_{col_index}") # Draw oval (circle) for endpoint, filled with color.

        def handle_canvas_click(event): # Define event handler for canvas clicks.
            if self.selected_color: # Check if a color is selected in the palette.
                col_index = event.x // self.cell_size # Calculate column index from click x-coordinate.
                row_index = event.y // self.cell_size # Calculate row index from click y-coordinate.
                if SATHelper.is_valid_position(self.grid_size_value, row_index, col_index): # Validate if clicked position is within grid bounds.
                    current_color = self.cell_colors.get((row_index, col_index)) # Get current color of the clicked cell.
                    if current_color: # If cell already has a color (endpoint).
                        self.cell_colors[(row_index, col_index)] = None # Remove the color (set to None).
                        self.canvas.delete(f"endpoint_{row_index}_{col_index}") # Delete the endpoint circle from the canvas.
                    else: # If cell does not have a color.
                        self.cell_colors[(row_index, col_index)] = self.selected_color # Set the cell color to the selected color.
                        self.canvas.delete(f"endpoint_{row_index}_{col_index}") # Ensure no existing endpoint circle is present (cleanup, though should not be necessary).
                        draw_endpoint_circle(row_index, col_index, self.selected_color) # Draw a new endpoint circle with the selected color.

        self.canvas.bind("<Button-1>", handle_canvas_click) # Bind left mouse button click event to handle_canvas_click function.

        for (row_index, col_index), color_name in saved_cell_colors.items(): # Iterate through saved cell colors.
            if color_name: # If cell had a color before refresh.
                self.cell_colors[(row_index, col_index)] = color_name # Restore the color in cell_colors dictionary.
                draw_endpoint_circle(row_index, col_index, color_name) # Redraw the endpoint circle for this cell.

        if self.decoded_solution: # Check if a solution is already decoded.
            self._draw_solution_lines() # If yes, redraw the solution lines to ensure they are visible on the refreshed grid.

    def _generate_puzzle_string(self):
        """
        Generates a puzzle string representation from the current state of the GUI grid.
        Iterates through the cell_colors dictionary, and for each cell that has a color assigned (endpoint),
        it gets the mnemonic character for that color and places it in the puzzle string.
        Empty cells (no color assigned) are represented by '.' in the puzzle string.
        The puzzle string is formatted as a multi-line string, with each line representing a row of the grid.

        Returns:
            str: A multi-line string representation of the puzzle, suitable for parsing by PuzzleParser.
        """
        puzzle_chars_grid = [['.' for _ in range(self.grid_size_value)] for _ in range(self.grid_size_value)] # Initialize a 2D list of characters, filled with '.' for empty cells.
        for (row_index, col_index), color_name in self.cell_colors.items(): # Iterate through the cell_colors dictionary.
            if color_name: # Check if a color is assigned to the cell (it's an endpoint).
                if color_name in FlowFreeConstants.COLOR_NAMES.values(): # Validate if the color name is in the list of known color names (safety check).
                    mnemonic_char = list(FlowFreeConstants.COLOR_NAMES.keys())[ # Get the mnemonic character corresponding to the color name.
                        list(FlowFreeConstants.COLOR_NAMES.values()).index(color_name)] # Find the index of color_name in COLOR_NAMES values and use it to get the key (mnemonic).
                    puzzle_chars_grid[row_index][col_index] = mnemonic_char # Set the mnemonic character in the puzzle_chars_grid at the corresponding row and column.
        return "".join("".join(row) + "\n" for row in puzzle_chars_grid) # Join the 2D list of characters into a multi-line string, with rows separated by newline characters.

if __name__ == '__main__':
    FlowFreeGUI() # Create and run the FlowFreeGUI application when the script is executed directly.
