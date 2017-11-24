# Polynomial-Time Reformulations of LTL Termporally Extended Goals into Final-State Goals

This code implements the article by Torres-Baier (https://www.ijcai.org/Proceedings/15/Papers/242.pdf):
given a pddl domain, a pddl problem and a goal expressed in LTLf, then it provides a new domain and a new problem. In particular, it returns a classical problem in which has been encoded the LTLf goal.

It has been implemented in Python3.5.


Usage:    

            python ./Translator.py domain.pddl problem.pddl [MODE]
            MODE = 0 | 1
            MODE = 0 means that the old problem goal is not kept
            MODE = 1 means that the old problem goal is put in AND with the LTL_f goal
          
          
            example: python ./Translator.py sokoban-domain.pddl sokoban-p01.pddl 1

Input format for the LTL_f formula:

            a
            not a
            a and b 
            a or b
            X (a) = next
            WX (a) = weak next
            G (a) = globally
            (a) U (b) = until
            (a) R (b) = release
