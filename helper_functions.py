# helper functions
# inset for strings
def insert_str(letter,index, string):
    return string[:index] + letter + string[index:]

def remove_str(index, string):
    return string[:index] + string[index+1:]


# find index of first occurence of a character in a string within a range of indices
def find_index_of_char_within_range(string, char, start, end):
    for i in range(start, end):
        if string[i] == char:
            return i
    return -1

# replace a letter at a specific index in a string
def replace_at_index(letter, index, string):
    return string[:index] + letter + string[index+1:]

# count number of characters in a string within a range of indices
def count_within_range(string, char, start, end):
    num = 0
    for i in range(start, end):
        if string[i] == char:
            num += 1
    return num

# replace all occurences of a character in a string within a range of indices
def replace_within_range(char, replacement, start, end, string):

    if end +2< len(string):
        end = end +2
    for i in range(start, end):
        if string[i] == char:
            string = replace_at_index(replacement, i, string)
    return string



