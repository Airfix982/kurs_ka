with open("p.txt", "r") as f:
    mod = int(f.readline())
R = Integers(mod)

with open("A.txt", "r") as f:
    A_data = [list(map(int, line.strip().split())) for line in f]

with open("b.txt", "r") as f:
    b_data = list(map(int, f.readline().strip().split()))

A = Matrix(R, A_data)
b = vector(R, b_data)

try:
    x = A.solve_right(b)
    print("SOLUTION_BEGIN")
    for val in x:
        print(int(val))
    print("SOLUTION_END")
except Exception as e:
    print("ERROR:", e)
