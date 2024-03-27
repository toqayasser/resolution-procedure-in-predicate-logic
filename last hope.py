# ∀x{[B(x)]→∃y{Q(x,y)∧¬P(y)}}
# ∧ ∃y{Q(x,y)∧Q(y,x)}
# ∧ ∀y{[¬B(y)]→¬E(x,y)}

# import "helper functions"
from helper_functions import *
import random , string

# 1. Eliminate implication:
def eliminate_implication(formula):
    # enter number of implication in formula
    number_of_implication = formula.count("→")
    for i in range(number_of_implication):
        # replace all implication with or
        formula = formula.replace("→", "∨",1)
        Lsqbracet_index = formula.find("[")
        formula = insert_str("¬", Lsqbracet_index, formula)
        # remove the first occurence of [ and ] in formula
        Lsqbracet_index = formula.find("[")
        formula = remove_str(Lsqbracet_index, formula)
        Rsqbracet_index = formula.find("]")
        formula = remove_str(Rsqbracet_index, formula)

    return formula

# test
# input: ∀x{[B(x)]→∃y{Q(x,y)∧¬P(y)}}∧¬∃y{Q(x,y)∧Q(y,x)}∧∀y{[¬B(y)]→¬E(x,y)}
# output: ∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧¬∃y{Q(x,y)∧Q(y,x)}∧∀y{¬¬B(y)∨¬E(x,y)}
# print(eliminate_implication("∀x{[B(x)]→∃y{Q(x,y)∧¬P(y)}}∧¬∃y{Q(x,y)∧Q(y,x)}∧∀y{[¬B(y)]→¬E(x,y)}"))


# 2. Move negation inward:
def move_negation_inward(formula):
    # not for exists
    count = formula.count("¬∃")
    for i in range(count):
        not_index = formula.find("¬∃")+2
        formula = formula.replace("¬∃", "∀",1)
        formula = insert_str("¬", not_index, formula)

    # not for all
    count = formula.count("¬∀")
    for i in range(count):
        not_index =formula.find("¬∀")+2
        formula = formula.replace("¬∀", "∃",1)
        formula = insert_str("¬", not_index, formula)

    # demorgan's law
    # output till now: ∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧∀y¬{Q(x,y)∧Q(y,x)}∧∀y{¬¬B(y)∨¬E(x,y)}
    count = formula.count("¬{")

    for i in range(count):
        not_index = formula.find("¬{")
        formula= formula.replace("¬{", "{¬",1)
        find_right_bracket = formula.find("}", not_index)

        and_index = find_index_of_char_within_range(formula, "∧", not_index, find_right_bracket)
        or_index = find_index_of_char_within_range(formula, "∨", not_index, find_right_bracket)
        if and_index >0 :
            formula = replace_at_index("∨¬", and_index, formula)
        elif or_index >0:
            formula = replace_at_index("∧¬", or_index, formula)

    return formula

# test
# input: ∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧¬∃y{Q(x,y)∧Q(y,x)}∧∀y{¬¬B(y)∨¬E(x,y)}
# output: ∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{¬¬B(y)∨¬E(x,y)}
# print(move_negation_inward("∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧¬∃y{Q(x,y)∧Q(y,x)}∧∀y{¬¬B(y)∨¬E(x,y)}"))


# 3. Remove double not
def remove_double_not(formula):
    number_of_double_not = formula.count("¬¬")
    for i in range(number_of_double_not):
        formula = formula.replace("¬¬", "")
    return formula

# test
# input: ∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{¬¬B(y)∨¬E(x,y)}
# output: ∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{B(y)∨¬E(x,y)}
# print(remove_double_not("∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{¬¬B(y)∨¬E(x,y)}"))

# 4.Skolemization for existential quantifiers.

def skolemization(formula):
    # find ∃
    count = formula.count("∃")

    for i in range(count):
        exists_index = formula.find("∃")
        exists_var = formula[exists_index+1]

        forall_var=""
        # find the first  ∀ before ∃ by inverse iteration
        for j in reversed(range(exists_index)):
            if formula[j] == "∀":
                forallvar = formula[j+1]
                break

        #     replace ∃ variable with new variable in range next {}
        find_right_bracket = formula.find("}", exists_index)
        new_var = f"f({forallvar})"
        formula = replace_within_range(exists_var, new_var, exists_index+2, find_right_bracket , formula)

    #     remove ∃ and its variable
        formula = remove_str(exists_index, formula)
        formula = remove_str(exists_index, formula)

    return formula

# test
# input: ∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{B(y)∨¬E(x,y)}
# output: ∀x{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{B(y)∨¬E(x,y)}
# print(skolemization("∀x{¬B(x)∨∃y{Q(x,y)∧¬P(y)}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{B(y)∨¬E(x,y)}"))

# 5. Standardize variable scope.
def standardize_variable_scope(formula):
    forall_variables = [] # x, y, y
    dict_of_indcies = {} # x: 1, y: 2
    # find all variables of ∀
    for i in range(len(formula)):
        if formula[i]=="∀":
            forall_variables.append(formula[i+1])
            dict_of_indcies[formula[i+1]] = i

    not_unique_variable = []# y ,y
    # find not unique variables by removing all unique variables from forall_variables
    for i in range(len(forall_variables)):
        if forall_variables.count(forall_variables[i]) > 1:
            not_unique_variable.append(forall_variables[i])



    not_unique_variable=list(set(not_unique_variable))

  # finding the range of changing variables in formula and replacing them with unique variables
    for i in range(len(not_unique_variable)):
        start = dict_of_indcies[not_unique_variable[i]]
        end = formula.find("}", start)
        # replace all variables with unique variables
        formula = replace_within_range(not_unique_variable[i], chr(97 + i), start, end, formula)
    return formula
# test
# input:  ∀x{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{B(y)∨¬E(x,y)}
# output:∀x{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀a{B(a)∨¬E(x,a)}
# print(standardize_variable_scope("∀x{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀y{B(y)∨¬E(x,y)}"))

# 6.The prenex form (obtained by moving all quantifiers to the left of the
# formula.)
def prenex_form(formula):
    # find all for all variables
    forall_variables = []

    # find all variables of ∀
    for i in range(len(formula)):
        if formula[i] == "∀":
            forall_variables.append(formula[i ]+formula[i+1])

    # removing all variables of ∀ from formula
    for i in range(len(forall_variables)):
        formula = formula.replace(forall_variables[i], "")



    # add all variables of ∀ at the beginning of formula
    forall_variables.reverse() #vx, vy, va
    for i in range(len(forall_variables)):
        formula = forall_variables[i] + formula


    return formula

# test
# input:  ∀x{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀a{B(a)∨¬E(x,a)}
# output:∀x∀y∀a{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}
# print(prenex_form("∀x{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧∀y{¬Q(x,y)∨¬Q(y,x)}∧∀a{B(a)∨¬E(x,a)}"))

#7.Convert to conjunctive normal form (CNF). whcih is a conjunction of clauses, where a clause is a disjunction of literals.
def convert_to_cnf(formula):
    # find ∨{ in formula
    count = formula.count("∨{")

    for i in range(count):
        or_index = formula.find("∨{")

        find_Lbracket_index = 0
        # find the first { before ∨{ by inverse iteration
        for j in reversed(range(or_index)):
            if formula[j] == "{":
                find_Lbracket_index = j
                break

        # find predicate
        find_predicate = formula[find_Lbracket_index: or_index+1] #{¬B(x)∨

        # find  scope of replacement
        L_bracket_index = or_index+1
        R_bracket_index = formula.find("}", L_bracket_index)

        #replacment preparation
        find_and_index = find_index_of_char_within_range(formula, "∧", L_bracket_index, R_bracket_index)
        scope = formula[L_bracket_index: R_bracket_index+1]
        lHS = find_predicate+ formula[L_bracket_index+1: find_and_index]+"}"
        RHS =find_predicate + formula[find_and_index+1: R_bracket_index+1]

        replacement = lHS+"∧"+RHS

        formula = formula.replace(find_predicate+scope+"}", replacement)

    return formula

# test
# input:  ∀x∀y∀a{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}
# output: ∀x∀y∀a{¬B(x)∨Q(x,f(x))}∧{¬B(x)∨¬P(f(x))}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}
# print(convert_to_cnf("∀x∀y∀a{¬B(x)∨{Q(x,f(x))∧¬P(f(x))}}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}"))



# 8.Eliminate universal quantifiers.

def eliminate_universal_quantifiers(formula):
    # count all variables of ∀
    count = formula.count("∀")
    formula = formula[count*2:]
    return formula

# test
# input:  ∀x∀y∀a{¬B(x)∨Q(x,f(x))}∧{¬B(x)∨¬P(f(x))}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}
# output: {¬B(x)∨Q(x,f(x))}∧{¬B(x)∨¬P(f(x))}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}
# print(eliminate_universal_quantifiers("∀x∀y∀a{¬B(x)∨Q(x,f(x))}∧{¬B(x)∨¬P(f(x))}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}"))


# {¬B(x)∨Q(x,f(x))}
# ∧{¬B(x)∨¬P(f(x))}
# ∧{¬Q(x,y)∨¬Q(y,x)}
# ∧{B(a)∨¬E(x,a)}


#9. Turn conjunctions into clauses in a set, and rename variables so that no
# clause shares the same variable name.

'''''

def turn_conjunctions_into_clauses_renameBetweenClauses(formula):
    # Split the formula by the conjunction symbol '∧'
    clauses = formula.split("∧")
    new_clauses = []

    used_characters = set()  # Used to track characters already used for replacement
    character_map = {}  # Map original characters to their replacements

    for clause in clauses:
        new_clause = ""
        for char in clause:
            if char.isalpha() and char != "f" and char.islower():
                if char not in character_map:
                    # Pick a new character that has not been used yet
                    available_characters = [c for c in string.ascii_lowercase if c not in used_characters]
                    if available_characters:
                        new_char = random.choice(available_characters)
                        character_map[char] = new_char
                        used_characters.add(new_char)
                    else:
                        # In case we run out of characters to use
                        print("No more available characters to use for replacement.")
                        return
                new_clause += character_map[char]
            else:
                new_clause += char
        new_clauses.append(new_clause)

    # Print each clause on a separate line
    for clause in new_clauses:
        print(clause)

    return new_clauses
'''''


def turn_conjunctions_into_clauses_renameBetweenClauses(formula):
    used_characters = set()  # Used to track characters already used for replacement
    new_formula = ""

    for char in formula:
        if char.isalpha() and char != "f" and char.islower():
            if char not in used_characters:
                # If the character is not used for replacement yet, keep it unchanged
                new_formula += char
                used_characters.add(char)
            else:
                # If the character is already used for replacement, choose a new character
                new_char = random.choice([c for c in string.ascii_lowercase if c not in used_characters])
                new_formula += new_char
                used_characters.add(new_char)
        else:
            # If the character is not a lowercase letter or is 'f', keep it unchanged
            new_formula += char

    new_formula=new_formula.split("∧")
    return new_formula

# Example formula
formula = "{¬B(x)∨Q(x,f(x))}∧{¬B(x)∨¬P(f(x))}∧{¬Q(x,y)∨¬Q(y,x)}∧{B(a)∨¬E(x,a)}"

# Call the function with the example formula
new_formula = turn_conjunctions_into_clauses_renameBetweenClauses(formula)
print(new_formula)
