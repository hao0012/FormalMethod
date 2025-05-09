""" Knapsack problem


The knapsack problem is a typical optimization problem，which has been
studied for hundred of years. The problem is: given a set of items, each
item has a weight and a value, determine the number of items such that the
total weight is less than a given limit and the total value is as large
as possible. There are a number of sub-problems of the knapsack problem:
0-1 knapsack problem, complete knapsack problem, multiply knapsack problem,
multi-dimensional knapsack problem and so on.

This problem is NPC, and for more background information of the
knapsack problem, please refer to:
https://en.wikipedia.org/wiki/Knapsack_problem
"""

import time
from pathlib import Path
import unittest

from z3 import *


# 0-1 Knapsack problem
#
# The 0-1 knapsack problem is
# There are n items, with specific weight
#   W = {w1, ..., wn}
# and value:
#   V = {v1, ..., vn}
# For a given knapsack of maximum capacity C, how to choose some items
# such that:
#   wi+...+wk <= C
# and with maximum value
#   max(vi+...+vk).

# Here is a concrete example:
#   W = {4, 6, 2, 2, 5, 1}
#   V = {8, 10, 6, 3, 7, 2}
# the result is: we should select the first, second, and third items, and
# the total value is:
#   8+10+6 = 24

# The 0-1 knapsack problem is often solved by the dynamic
# programming, and here is a DP algorithm:
def zero_one_knapsack_dp(weights, values, cap):
    def knapsack_dp_do(rest_cap, index):
        if rest_cap <= 0 or index <= 0:
            return 0

        if weights[index - 1] > rest_cap:
            return knapsack_dp_do(rest_cap, index - 1)

        value_1 = knapsack_dp_do(rest_cap, index - 1)
        value_2 = knapsack_dp_do(rest_cap - weights[index - 1], index - 1)

        if value_1 >= (value_2 + values[index - 1]):
            return value_1

        return value_2 + values[index-1]

    start = time.time()
    result = knapsack_dp_do(cap, len(weights))
    print(f"zero_one_knapsack_dp solve {len(weights)} items by time {(time.time() - start):.6f}s")
    return result


# But it's more natural and much easier to solve knapsack with the 0-1 ILP theory:
def zero_one_knapsack_lp(weights, values, cap, verbose=False):
    # create a new solver, but
    solver = Optimize()

    # the decision variables
    flags = [Int(f"x_{i}") for i in range(len(weights))]
    # print(flags)

    # flags are 0-1
    for flag in flags:
        solver.add(Or(flag == 0, flag == 1))

    # @Exercise 15: solve the 0-1 knapsack problem by using 0-1 ILP
    # construct the constraint
    #   \sum_i weights[i] * flags[i] <= cap
    # and the the target
    #   \sum_i values[i] * flags[i]
    # Your code here:
    wf = []
    for i in range(len(weights)):
        wf.append(flags[i] * weights[i])
    solver.add(sum(wf) <= cap)

    vf = []
    for i in range(len(values)):
        vf.append(flags[i] * values[i])
    solver.maximize(sum(vf))

    start = time.time()
    result = solver.check()
    print(f"zero_one_knapsack_lp solve {len(weights)} items by time {(time.time() - start):.6f}s")

    if result == sat:
        model = solver.model()

        # print the chosen items
        if verbose:
            print("\n".join([f"Index: {index}, Weight: {weights[index]}, Value: {values[index]}"
                             for index, flag in enumerate(flags) if model[flag] == 1]))

        return True, sum([values[index] for index, flag in enumerate(flags) if model[flag] == 1])

    return False, result


# The complete knapsack problem assumes that the number of items of all kinds is unlimited,
# your can choose one kind of item any times.
# So we need to declare a variable for each kind of item have chosen by amount
def complete_knapsack_lp(weights, values, cap, verbose=False):
    solver = Optimize()

    # @Exercise 16: solve the complete knapsack problem by using LP
    # note that flags[i] will be a integer and flags[i] >= 0
    # construct the constraint
    #   \sum_i weights[i] * flags[i] <= cap
    # and the the target
    #   \sum_i values[i] * flags[i]
    # Your src here:
    # create a new solver, but

    flags = [Int(f"x_{i}") for i in range(len(weights))]

    # flags are 0-inf
    for flag in flags:
        solver.add(flag >= 0)
    wf = []
    for i in range(len(weights)):
        wf.append(flags[i] * weights[i])
    solver.add(sum(wf) <= cap)

    vf = []
    for i in range(len(values)):
        vf.append(flags[i] * values[i])
    solver.maximize(sum(vf))

    start = time.time()
    result = solver.check()
    print(f"complete_knapsack_lp solve {len(weights)} items by time {(time.time() - start):.6f}s")

    if result == sat:
        model = solver.model()

        # print the chosen items
        if verbose:
            print("\n".join([f"Index: {index}, Weight: {weights[index]}, Value: {values[index]}, Amount: {model[flag]}"
                             for index, flag in enumerate(flags) if model[flag].as_long() > 0]))
        return True, sum([values[index] * model[flag].as_long() for index, flag in enumerate(flags)])
    
    return False, result
   

def get_large_test():
    # this test data is fetched from:
    # https://people.sc.fsu.edu/~jburkardt/datasets/knapsack_01/knapsack_01.html
    # the expect maximum value should be: 13549094
    def read_numbers_from_file(file_path):
        with Path(file_path).open(mode="r") as fp:
            content = fp.readlines()
            return [int(x.strip()) for x in content]

    file_folder = Path(__file__).parent.resolve()
    return (read_numbers_from_file(file_folder / "p08_w.txt"),
            read_numbers_from_file(file_folder / "p08_p.txt"))


class TestKnapsack(unittest.TestCase):

    def test_zero_one_knapsack_1(self):
        W = [4, 6, 2, 2, 5, 1]
        V = [8, 10, 6, 3, 7, 2]
        C = 12
        
        res_dp = zero_one_knapsack_dp(W, V, C)
        res_lp = zero_one_knapsack_lp(W, V, C, verbose=True)
        
        self.assertEqual(res_dp, res_lp[1])
        
    def test_zero_one_knapsack_2(self):
        W = [23, 26, 20, 18, 32, 27, 29, 26, 30, 27]
        V = [505, 352, 458, 220, 354, 414, 498, 545, 473, 543]
        C = 67

        res_dp = zero_one_knapsack_dp(W, V, C)
        res_lp = zero_one_knapsack_lp(W, V, C, verbose=True)
        
        self.assertEqual(res_dp, res_lp[1])
        
    def test_complete_knapsack(self):
        W = [23, 26, 20, 18, 32, 27, 29, 26, 30, 27]
        V = [505, 352, 458, 220, 354, 414, 498, 545, 473, 543]
        C = 133
        
        res_lp = complete_knapsack_lp(W, V, C, verbose=True)
        self.assertEqual(res_lp[1], 2936)
    
    def test_large_case(self):
        W, V = get_large_test()
        C = 6404180
        
        # @Exercise 17: compare the efficiency of the DP and the
        # LP algorithm, by running your program on a larger data.
        # what's your observation? What conclusion you can draw from these data?
        # Your code here:
        print("solution of Exercise 17: ")
        zero_one_knapsack_dp(W, V, C)
        zero_one_knapsack_lp(W, V, C)
        
        
if __name__ == '__main__':
    unittest.main()
