import itertools
import random
import numpy as np

# Creates all possible automaton
def bjorn_possibilities2():
    edge = [e for e in itertools.product((0,1), repeat = 3)]

    assert (edge[0] == (0,0,0))
    assert (edge[5] == (1,0,1))
    assert (len(edge) == 8)

    totEdges = []

    for accept in range (0,2):
        for numEdges in range (1,9):
            j = 0
            for edgeTuple in itertools.product((0,1), repeat = 8):
                myEdges = []
                if edgeTuple.count(1) == numEdges:
                    for i in range(0, 8):
                        if edgeTuple[i] == 1:
                            myEdges.append(edge[i])
                    myEdges.append(accept)
                    totEdges.append(myEdges)
                    j += 1
    return totEdges


# Cycles through an automaton to check if it accepts a word
def delta_recursive(automata, initial_state, word):
    k = 0
    result = -1
    while k < len(automata) - 1:
        set1 = (automata[k][0], automata[k][1])
        set2 = (initial_state, word[0])

        if set1 == set2:
            result = automata[k][2]
            if len(word) > 1:
                return delta_recursive(automata, result, word[1:])
        k += 1

    return result


# Returns all possible automaton that work for a word=
def find_valid_item_recursive(word):
    all_auto = bjorn_possibilities2()
    return_vals = []

    for x in all_auto:
        result0 = delta_recursive(x, 0, word)
        if result0 == x[-1] or check_string_in_automaton(x, word):
            return_vals.append(x)

    return return_vals


# Returns all possible automaton that work for a set of words
def find_valid_set(string_set):
    solution_sets = []
    temp_set = []

    for x in string_set:
        solution_sets.append(find_valid_item_recursive(x))

    numSets = len(solution_sets)

    while numSets > 1:
        temp_set = intersect(solution_sets[numSets-1], solution_sets[numSets-2])
        solution_sets.pop()
        solution_sets.pop()
        solution_sets.append(temp_set)
        numSets -= 1

    if solution_sets == []:
        return solution_sets
    else:
        return solution_sets[0]


# Returns a list of all possible subsets of a string set, which each sublist containing subset of strings and
# all valid automaton
def find_subsets(string_set, num_of_sets):
    #Example string_set == set([(0,0,1),(1,1,1),(0,0,0),(1,0,1)])
    # num_of_sets == len(string_set)
    #accept subset set([(0,0,1),(1,1,1)])
    #Want an automaton that accepts "subset" but not (0,0,0)
    #and not (1,0,1)
    #we don't care whether it accepts (0,1,0) say
    set_of_solution_sets = []
    index = 0
    for k in range(0, num_of_sets + 1):
        for subset in list(itertools.combinations(string_set, k)):
            solutions = find_valid_set(subset)
            if solutions != []:
                sub_sol = []
                sub_sol.append(subset)
                sub_sol.append(solutions)
                set_of_solution_sets.append(sub_sol)
                index += 1

    return set_of_solution_sets


# Returns a unique automaton for each subset of a string set
def find_VC(string_set, num_of_sets):
    data = find_subsets(string_set, num_of_sets)
    proper_data = check_valid_for_auto(data)

    for one in proper_data:
        if one[1] == []:
            print("There is no solution")
            return

    solution = []
    for stuff in proper_data:
        sub_solution = []
        i = random.randint(0, len(stuff[1]) - 1)
        sub_solution.append(stuff[0])
        sub_solution.append(stuff[1][i])
        print(sub_solution)
        solution.append(sub_solution)

    print(solution)
    return solution


# Filters valid automaton for each subset, such that automaton only work for a certain subset
def check_valid_for_auto(list_of_subset_solutions):
    for i, j in unique_subsets(len(list_of_subset_solutions)):
        first_subset = list_of_subset_solutions[i]
        other_subset = list_of_subset_solutions[j]
        temp_index = 0
        if i != j:
            for k in range(len(first_subset[1])):
                if check_duplicate_words(first_subset[1][temp_index], other_subset[0]) is True and len(
                        first_subset[0]) == len(other_subset[0]):
                    first_subset[1].remove(first_subset[1][temp_index])
                    temp_index -= 1
                temp_index += 1

    return list_of_subset_solutions


# Checks if a word works for an automaton
def check_duplicate_words(automaton, words):
    ret_val = True
    counter0 = 0
    counter1 = 0

    for word in words:
        result0 = delta_recursive(automaton, 0, word)
        if result0 == automaton[-1]:
            counter0 += 1
        elif result0 != automaton[-1]:
            ret_val = False

    if len(words) == 1:
        result1 = check_string_in_automaton(automaton, words[0])
        ret_val = result1
    else:
        for word in words:
            result1 = check_string_in_automaton(automaton, word)
            if result1 == True:
                counter1 += 1
            elif result1 == False:
                ret_val = False

    if len(words) == counter1:
        ret_val = True

    return ret_val


# Helper function to check if a word works for an automaton through matrices
def check_string_in_automaton (automaton, string):
    matrix_0 = np.zeros([2,2], dtype= int)
    matrix_1 = np.zeros([2,2], dtype= int)
    matrix_list = []
    last_result = []

    for tup in itertools.islice(automaton, len(automaton) - 1):
        if tup[1] == 0:
            matrix_0[tup[2]][tup[0]] = 1
        else:
            matrix_1[tup[2]][tup[0]] = 1

    matrix_list.append(matrix_0)
    matrix_list.append(matrix_1)

    reversed_string = string[::-1]

    if len(reversed_string) < 3:
        last_result = np.matmul(matrix_list[reversed_string[0]], matrix_list[reversed_string[1]])
        last_result = np.matmul(last_result, np.array([[1],[0]]))
    else:
        last_result = multiply(matrix_list, np.matmul(matrix_list[reversed_string[0]], matrix_list[reversed_string[1]]), reversed_string[2:])

    if last_result[automaton[-1]] > 0:
        return True
    else:
        return False


# Helper function to multiply a set of matrices together
def multiply(my_list, some_result, reversed_string):
    inter_result = np.matmul(some_result, my_list[int(reversed_string[0])])

    if len(reversed_string) == 1:
        inter_result = np.matmul(inter_result, np.array([[1], [0]]))
        return inter_result
    else:
        return multiply(my_list, inter_result, reversed_string[1:])


# Helper function for check_valid_auto() for iterating through all sets, for each set
def unique_subsets(n):
    for i in range(n):
        for j in range(n):
            yield i, j


# Helper function for eliminating repeat automaton in find_valid_set()
def intersect(list1, list2):
    tup1 = map(tuple, list1)
    tup2 = map(tuple, list2)

    return list(map(list, set(tup1).intersection(tup2)))

he  = (0,1,0,0,0,1,1,1,0,1,1,0)#,1,1,0,1,1,1,0)
u = (0,1,0,0,1,1,1,1,0,0,1,1)#,1,1,0,1,1,1,0)
ni = (0,1,0,1,0,1,0,1,0,1,0,1)
#ri = (0,1,1,1,0,0,0,1)


# Main function
if __name__ == '__main__':
    find_VC((he, u, ni), 3)  # find_VC(((0,0,1,1,0,0,0,1,1,1,0,1,1,1,0),(0,0,1,1,0,0,1,1,1,1,0,1,1,1,0)), 2)
