#   Usage: python .\Translator.py input_domain_file input_problem_file goal_mode

import codecs
import sys
from LTLf_translator import obtain_automaton_states
from LTLf_translator import populate_subformula
from LTLf_translator import remove_spaces


OUTPUT_DOMAIN = "C:\\Users\Riccardo\Documents\shared\\test_TorresBaier\\new_domain.pddl"
OUTPUT_PROBLEM = "C:\\Users\Riccardo\Documents\shared\\test_TorresBaier\\new_problem.pddl"
DEFINE = "define"
REQUIREMENTS = ":requirements"
PARAMETERS = ":parameters"
PRECONDITION = ":precondition"
PREDICATES = ":predicates"
EFFECT = ":effect"
ACTION = ":action"
PRED = 0
ACT = 1
WORLD_MD = "(world)"
NOT_WORLD_MD = "(not (world))"
OK = "(ok)"
COPY = "(copy)"

DEFAULT_GOAL_MODE = 0
KEEP_GOAL_MODE = 1

S_PREDICATES = ["(copy)", "(sync)", "(world)", "(ok)"]
WORLD_ACTION = ["()", "(and (sync) (ok))", "(and (world) (not (sync)))"] # The part related to q^s is missing

INITIAL_STATE_COMPLETION = "\t\t(q0)\n" \
                           "\t\t(copy)\n" \
                           "\t\t(ok)\n"

LIT = "lit"
NOT = "not"
AND = "and"
OR = "or"
NEXT = "X"
WEAK_NEXT = "WX"
UNTIL = "U"
RELEASE = "R"
GLOBALLY = "G"
EVENTUALLY = "F"
OPERATORS = [AND, OR, NEXT, WEAK_NEXT, UNTIL, GLOBALLY, EVENTUALLY, RELEASE]

predicates = []
actions = {}


#   Auxiliary method for populating the actions dictionary
def populate_actions(action_name, split, row):
    first = True
    action_part = ""
    for elem in split:
        if ";" in elem:
            break
        if PARAMETERS not in elem and EFFECT not in elem and PRECONDITION not in elem:
            if not first:
                action_part += " "
            else:
                first = False
            action_part = action_part + elem
    if action_part != "":
        action = actions[action_name]
        if row == PARAMETERS:
            param = action[0]
            if param != "" and action_part != ")":
                param += " "
            actions[action_name][0] = param + action_part
        elif row == PRECONDITION:
            precondition = action[1]
            if precondition != "" and action_part != ")":
                precondition += " "
            actions[action_name][1] = precondition + action_part
        elif row == EFFECT:
            effect = action[2]
            if effect != "" and action_part != ")":
                effect += " "
            actions[action_name][2] = effect + action_part


def is_in_map(subformula, q_map):
    if subformula in q_map.keys():
        return True
    return False


# Auxiliary method that is used to find out the alpha and beta for a particular operator
# It is used for binary operators, i.e. and, or, until, weak until
def find_alpha_beta(subformula, formula_type, inverted_map):
    split = subformula.replace("(", "( ").replace(")", " )").split()
    parenthesis = 0
    counter = 0
    pointer = [0, sys.maxsize]  # pointer = (position of the operator, number of parenthesis)
    for elem in split:
        if elem == "(":
            parenthesis += 1
        elif elem == ")":
            parenthesis -= 1
        elif elem == formula_type and parenthesis < pointer[1]:
            pointer = [counter, parenthesis]
        counter += 1
    alpha = remove_spaces(populate_subformula(split, 0, pointer[0]))
    beta = remove_spaces(populate_subformula(split, pointer[0] + 1, len(split)))
    if not is_in_map(alpha, inverted_map):
        alpha = manipulate_formula(alpha, inverted_map)
    if not is_in_map(beta, inverted_map):
        beta = manipulate_formula(beta, inverted_map)
    return [alpha, beta]


# Auxiliary method for finding the subformula of a particular unary operator,
# i.e. next, weak next, eventually and globally
def find_alpha(formula_type, subformula):
    alpha = subformula[len(formula_type)+2:len(subformula)-1]
    return alpha


# Auxiliary method for understanding if a formula in in the map even if in another form, e.g.
# a and b may be in the map as (a and b), it's the same formula! and vice versa
def manipulate_formula(subformula, q_map):
    new_subformula = ""
    if subformula[:1] == "(" and is_in_map(subformula[1:len(subformula)-1], q_map):
        new_subformula = subformula[1:len(subformula) - 1]
    elif is_in_map("(" + subformula + ")", q_map):
        new_subformula = "(" + subformula + ")"
    else:
        print("Error: the formula " + subformula + " is not in the inverted map")
        exit(-1)
    return new_subformula


# Here we add new fluents
# F' = F U Q U Q_S U {ok, sync, world, copy}
def add_predicates(q, goal_mode):
    predicates.extend(S_PREDICATES)     # F U {ok, sync, world, copy}
    for state in q:
        predicates.append("(" + state + ")")        # Q
        predicates.append("(" + state + "_s)")      # Q_S
    # This is a dummy predicate that will be true when all
    # q in Q are false
    predicates.append("(all_false)")

    # This is very useful for avoiding failure of Processing Axioms. Putting too many goal condition brings to failure.
    # So we take the old propositional goal and we put it as a precondition for this action. If the goal is reached and
    # the temporal constraints are satisfied, then we have done. Instead of adding to the constraint F (and of goal
    # condition, we put simply this goal_reached into the final goal.
    if goal_mode == KEEP_GOAL_MODE:
        predicates.append("(goal_reached)")


# This method modifies the O_w actions in terms of precondition and effect
def modify_actions(goal_mode, old_goal):
    for name in actions.keys():
        action = actions[name]
        #  precondition(a') = precondition(a) U {ok, world}
        precondition = action[1]
        if precondition[:4] == "(and":
            new_precondition = precondition[:len(precondition)-1] + " " + WORLD_MD + " " + OK + ")"
        else:
            new_precondition = "(and (" + precondition[1:] + " " + WORLD_MD + " " + OK + ")"
        action[1] = new_precondition

        # effect(a') = effect(a) U {copy, - world}
        effect = action[2]
        if effect[:4] == "(and":
            new_effect = effect[:len(effect)-1] + " " + COPY + " " + NOT_WORLD_MD + ")"
        else:
            new_effect = "(and (" + effect[1:] + " " + WORLD_MD + " " + OK + ")"
        action[2] = new_effect
    actions["world"] = WORLD_ACTION
    if goal_mode == KEEP_GOAL_MODE:
        gr_precondition = old_goal[:len(old_goal)-1] + "(world) (ok))"
        gr_effect = "(goal_reached)"
        actions["set_goal_reached"] = ["()", gr_precondition, gr_effect]


def add_sync_actions(q, automaton_map, inverted_map):

    world_precondition = "(and (sync) (ok)"
    not_copy_precondition = "(and (copy) (ok)"
    not_copy_effect = "(and (not (copy)) (sync))"

    # add copy actions
    for state in q:
        number = state[1:]
        not_copy_precondition += " (not (" + state + "))"
        copy_precondition = "(and (copy) (ok) (" + state + "))"
        copy_effect = "(and (" + state + "_s) (not (" + state + ")))"
        actions["copy_" + number] = ["()", copy_precondition, copy_effect]
        world_precondition += " (not (" + state + "_s))"
    not_copy_precondition += ")"

    # This action is used in order to switch from copy mode to sync mode
    # It will be executed iff all q_i are false
    actions["not_copy"] = ["()", not_copy_precondition, not_copy_effect]

    world_precondition += ")"
    world_effect = "(and (world) (not (sync)))"
    set_all_false_precondition = "(and (world) (ok)"

    for state in q:
        parameters = "()"
        precondition = "(and (sync) (ok) (" + state + "_s))"
        if state != "qf":
            set_all_false_precondition += " (not (" + state + "))"
            state_tuple = automaton_map[state]
            formula_type = state_tuple[1]
            name = "trans_" + formula_type + "_" + state[1:]
            subformula = state_tuple[0]
            if formula_type == LIT:
                neg_literal = False
                if subformula.split()[0] == "not":
                    subformula = subformula.replace("not ", "not (")
                    neg_literal = True
                precondition = precondition[:len(precondition)-1] + " (" + subformula + "))"
                if neg_literal:
                    precondition += ")"
                effect = "(not (" + state + "_s))"
                actions[name] = ["()", precondition, effect]
            elif formula_type == AND:
                subformulas = find_alpha_beta(subformula, AND, inverted_map)
                alpha = subformulas[0]
                beta = subformulas[1]
                effect = "(and (" + inverted_map[alpha] + "_s) (" + inverted_map[beta] + "_s) (not (" + state + "_s)))"
                actions[name] = [parameters, precondition, effect]
            elif formula_type == OR:
                name_1 = name + "_1"
                name_2 = name + "_2"
                subformulas = find_alpha_beta(subformula, OR, inverted_map)
                alpha = subformulas[0]
                beta = subformulas[1]
                effect_1 = "(and (" + inverted_map[alpha] + "_s) (not (" + state + "_s)))"
                effect_2 = "(and (" + inverted_map[beta] + "_s) (not (" + state + "_s)))"
                actions[name_1] = [parameters, precondition, effect_1]
                actions[name_2] = [parameters, precondition, effect_2]
            elif formula_type == NEXT:
                alpha = find_alpha(NEXT, subformula)
                effect = "(and (" + inverted_map[alpha] + ") (not (" + state + "_s)))"
                actions[name] = [parameters, precondition, effect]
            elif formula_type == WEAK_NEXT:
                name_1 = name + "_1"
                name_2 = name + "_2"
                effect_1 = "(and (qf) (not (" + state + "_s)))"
                alpha = find_alpha(WEAK_NEXT, subformula)
                effect_2 = "(and (" + inverted_map[alpha] + ") (not (" + state + "_s)))"
                actions[name_1] = [parameters, precondition, effect_1]
                actions[name_2] = [parameters, precondition, effect_2]
            elif formula_type == UNTIL:
                name_1 = name + "_1"
                name_2 = name + "_2"
                subformulas = find_alpha_beta(subformula, UNTIL, inverted_map)
                alpha = subformulas[0]
                beta = subformulas[1]
                effect_1 = "(and (" + inverted_map[beta] + "_s) (not (" + state + "_s)))"
                effect_2 = "(and (" + inverted_map[alpha] + "_s) (" + state + ") (not (" + state + "_s)))"
                actions[name_1] = [parameters, precondition, effect_1]
                actions[name_2] = [parameters, precondition, effect_2]
            elif formula_type == RELEASE:
                name_1 = name + "_1"
                name_2 = name + "_2"
                name_3 = name + "_3"
                subformulas = find_alpha_beta(subformula, RELEASE, inverted_map)
                alpha = subformulas[0]
                beta = subformulas[1]
                effect_1 = "(and (" + inverted_map[beta] + "_s) (qf) (not (" + state + "_s)))"
                effect_2 = "(and (" + inverted_map[beta] + "_s) (" + \
                           inverted_map[alpha] + "_s) (not (" + state + "_s)))"
                effect_3 = "(and (" + inverted_map[beta] + "_s) (" + state + ") (not (" + state + "_s)))"
                actions[name_1] = [parameters, precondition, effect_1]
                actions[name_2] = [parameters, precondition, effect_2]
                actions[name_3] = [parameters, precondition, effect_3]

            # This part is not explicit in the paper, but without this action we cannot write LTLf goals s.t.
            # F (a and b), F (have_gold and X (lose_gold)) etc..
            elif formula_type == EVENTUALLY:
                name_1 = name + "_1"
                name_2 = name + "_2"
                alpha = find_alpha(EVENTUALLY, subformula)
                beta = "X (" + subformula + ")"
                effect_1 = "(and (" + inverted_map[alpha] + "_s) (not (" + state + "_s)))"
                effect_2 = "(and (" + inverted_map[beta] + "_s) (not (" + state + "_s)))"
                actions[name_1] = [parameters, precondition, effect_1]
                actions[name_2] = [parameters, precondition, effect_2]

            # Same stuff for globally
            elif formula_type == GLOBALLY:
                alpha = find_alpha(GLOBALLY, subformula)
                beta = "WX (" + subformula + ")"
                effect = "(and (" + inverted_map[alpha] + "_s) (" + inverted_map[beta] + "_s) (not (" + state + "_s)))"
                actions[name] = [parameters, precondition, effect]

    actions["trans_f"] = ["()", "(and (sync) (ok) (qf_s))", "(and (not (qf_s)) (not (ok)))"]

    # add world action
    actions["world"] = ["()", world_precondition, world_effect]

    # add action that, when all q in Q are false, put the predicate all_false to true
    set_all_false_precondition += ")"
    set_all_false_effect = "(all_false)"
    actions["set_all_false"] = ["()", set_all_false_precondition, set_all_false_effect]


#   This method will be used for printing the new planning problem once the elements are modified.
#   The actions are printed in a random order because the dictionary is not sorted. This is not relevant
#   For the problem file, we have now only the goal saved as a string.
def print_new_domain(first_part, function_part):
    out_file = open(OUTPUT_DOMAIN, 'w')
    out_file.write(first_part)
    out_file.write("\t(:predicates\n")
    for predicate in predicates:
        out_file.write("\t\t" + predicate + "\n")
    out_file.write("\t)\n")
    out_file.write("\t" + str(function_part))
    for action in actions.keys():
        out_file.write("\t(:action " + action + "\n")
        out_file.write("\t\t:parameters " + actions[action][0] + "\n")
        out_file.write("\t\t:precondition " + actions[action][1] + "\n")
        out_file.write("\t\t:effect " + actions[action][2] + "\n")
        out_file.write("\t)\n")
    out_file.write(")")
    out_file.close()


def print_new_problem(new_problem, goal_mode):
    new_goal = "\t(:goal\n" \
               "\t\t(and (world) (ok) (all_false)"
    if goal_mode == KEEP_GOAL_MODE:
        new_goal += " (goal_reached)"
    new_goal += ")\n" \
                "\t)\n" \
                ")"
    out_file = open(OUTPUT_PROBLEM, 'w')
    out_file.write(new_problem)
    out_file.write(new_goal)
    out_file.close()


#   This method is used for parsing the domain.pddl file of the simplest form,
#   i.e. define, requirements, predicates and actions.
#   It stores define and requirements in two strings, predicates as a list (each element is a predicate with param)
#   and actions as a dictionary that has as key the action name and as value 3 strings: params, precondition and effect
#   (i.e. (action_name,[parameters, precondition, effect]))
def parse_domain(file_name):
    row = ""
    parsing_set = ""
    first_part = ""
    function_part = ""
    parenthesis_found = False
    with codecs.open(file_name, 'r') as file_handle:
        for line in file_handle:
            one_line = line.replace("\n", "")
            split = one_line.split()
            if len(split) > 0:
                if ";" in split[0]:
                    continue
                elif ":functions" in split[0]:
                    function_part += line
                elif PREDICATES in split[0]:
                            parsing_set = PRED
                elif ACTION in split[0]:
                    parsing_set = ACT
                    action_name = split[1]
                    actions[action_name] = ["", "", ""]
                elif parsing_set == PRED and len(split) > 0:
                    predicate = ""
                    first = True
                    for elem in split:
                        if ";" in elem:
                            break
                        if not first:
                            predicate += " "
                        else:
                            first = False
                        predicate += elem
                    if len(predicate) > 1:
                        predicates.append(predicate)
                elif parsing_set == ACT:
                    if split[0] == ")" and row == EFFECT:
                        if not parenthesis_found:
                            parenthesis_found = True
                            continue
                    else:
                        parenthesis_found = False
                        if PARAMETERS in split[0]:
                            row = PARAMETERS
                        elif EFFECT in split[0]:
                            row = EFFECT
                        elif PRECONDITION in split[0]:
                            row = PRECONDITION
                        populate_actions(action_name, split, row)
                else:
                    first_part += line
    return [first_part, function_part]


#   This method is used for parsing the problem.pddl file
#   In particular it copies all the file but the initial state, which is stored in another variable and that
#   will be completed with the missing part
def parse_problem(file_name, goal_mode):
    with codecs.open(file_name, 'r') as file_handle:
        initial_state_part = False
        initial_state = ""
        problem_part1 = ""
        old_goal = ""
        goal_part = False
        for line in file_handle:
            if initial_state_part:
                split = line.split()
                if len(split) == 1:
                    if split[0] == ")":
                        # break
                        initial_state_part = False
                        if goal_mode == DEFAULT_GOAL_MODE:
                            break
                        else:
                            continue
                initial_state += line
            elif goal_part:
                split = line.split()
                if len(split) == 1:
                    if split[0] == ")":
                        break
                old_goal += line
            elif "(:goal" in line:
                goal_part = True
                old_goal += line
            elif "(:init" in line:
                initial_state_part = True
                initial_state += line
            else:
                problem_part1 += line
    old_goal = old_goal.replace("(:goal", "").replace("\n", "").replace("\t", "")
    # Here we complete the initial state, i.e. I' = I U {q_g, copy, ok}
    new_initial_state = initial_state + INITIAL_STATE_COMPLETION + "\t)\n"
    return problem_part1 + new_initial_state, old_goal


def main():
    if len(sys.argv) < 3:
        print("Usage error!\n"
              "Correct usage: python .\Translator.py domain_file problem_file [goal_mode]")
        exit(-1)
    file_domain_name = sys.argv[1]
    file_problem_name = sys.argv[2]
    if len(sys.argv) < 4:
        goal_mode = DEFAULT_GOAL_MODE
    elif sys.argv[3] not in [str(DEFAULT_GOAL_MODE), str(KEEP_GOAL_MODE)]:
        print("Inserted goal mode is not defined. Write 0 for writing a completely new goal or 1 for keeping the"
              "old goal and add some temporal constraints")
        exit(-1)
    else:
        goal_mode = int(sys.argv[3])
    goal = input("Insert the LTLf goal\n")
    automaton_map = obtain_automaton_states(goal)
    q = []
    for key in automaton_map:
        q.append(key)
    q.append("qf")
    print("Automaton_map:\n" + str(automaton_map))
    inverted_map = {}
    for state in automaton_map:
        entry = automaton_map[state]
        q_formula = entry[0]
        inverted_map[q_formula] = state
    print("Inverted_map:\n" + str(inverted_map))

    unchanged_part = parse_domain(file_domain_name)
    first_part = unchanged_part[0]
    functions = unchanged_part[1]
    new_problem, old_goal = parse_problem(file_problem_name, goal_mode)
    add_predicates(q, goal_mode)
    modify_actions(goal_mode, old_goal)
    add_sync_actions(q, automaton_map, inverted_map)
    print_new_domain(first_part, functions)
    print_new_problem(new_problem, goal_mode)


main()
