import time
from z3 import *

def x_queen(num, is_print):
    solver = Solver()
    # the basic data structure:
    N = num
    board = [[Bool('b_{}_{}'.format(i, j)) for i in range(N)]
             for j in range(N)]

    # constraint 1: each row has just one queen:
    for i in range(N):
        rows = []
        for j in range(N):
            current_row = []
            current_row.append(board[i][j])
            for k in range(N):
                if k != j:
                    current_row.append(Not(board[i][k]))
            rows.append(And(current_row))
        solver.add(Or(rows))

    # Challenge: add constraints which describe each column has just one queen
    # constraint 2: each column has just one queen:
    for i in range(N):
        cols = []
        for j in range(N):
            current_col = []
            current_col.append(board[i][j])
            for k in range(N):
                if k != i:
                    current_col.append(Not(board[k][j]))
            cols.append(And(current_col))
        solver.add(Or(cols))

    # Challenge: add constraints which describe each diagonal has at most one queen
    # constraint 3: each diagonal has at most one queen:
    for i in range(N):
        diags = []
        for j in range(N):
            current_diag = []
            current_diag.append(board[i][j])
            d = i - j
            for k in range(N): # k - col == d
                if k == i:
                    continue
                col = k - d
                if 0 <= col < N:
                    current_diag.append(Not(board[k][col]))
            diags.append(And(current_diag))
        solver.add(Or(diags))
    
    # Challenge: add constraints which describe each anti-diagonal has at most one queen
    # constraint 4: each anti-diagonal has at most one queen:
    for i in range(N):
        anti_diags = []
        for j in range(N):
            current_anti_diag = []
            current_anti_diag.append(board[i][j])
            d = i + j
            for k in range(N):
                if k == i:
                    continue
                # k + col == d
                col = d - k
                if 0 <= col < N:
                    current_anti_diag.append(Not(board[k][col]))
            anti_diags.append(And(current_anti_diag))
        solver.add(Or(anti_diags))

    count = 0
    while solver.check() == sat:
        m = solver.model()
        if is_print:
            print(m)
        count += 1
        block = []
        for i in range(N):
            for j in range(N):
                if m.eval(board[i][j], True):
                    board[i][j] = board[i][j]
                else:
                    board[i][j] = Not(board[i][j])
                block.append(board[i][j])
        new_prop = Not(And(block))
        solver.add(new_prop)
        
    print("number of result: ",count)


if __name__ == '__main__':
    # Four Queen should have 2 set of solutions
    print("4 queen question: ")
    x_queen(4, True)

    print("8 queen question(only print execution time): ")
    start_time = time.perf_counter()
    x_queen(8, False)
    end_time = time.perf_counter()
    execution_time = end_time - start_time
    print(f"8 queen code execution time: {execution_time}s")

    print("10 queen question(only print execution time): ")
    start_time = time.perf_counter()
    x_queen(10, False)
    end_time = time.perf_counter()
    execution_time = end_time - start_time
    print(f"10 queen code execution time: {execution_time}s")