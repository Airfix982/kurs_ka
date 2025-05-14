import math
import numpy as np
import sympy
import subprocess

def countL(p, deg=1):
    L = math.e ** (deg * math.sqrt( math.log(p) * math.log( math.log(p) ) ))
    return int(L)

def countPI(x):
    return int(x / math.log(x))

def countExpectedCompFindAmount(N, c):
    t = countL(N, c + 1 / (2 * c)) * 1 / ( c * math.log( countL(N) ) )
    return int(t)

def preparing(p, c):
    B = countL(p, c)
    n = countPI(B)
    iterAmount = countExpectedCompFindAmount(p, c)
    print('Parameter B: ', B)
    print('Necessary B-smoothes amount: ' ,n)
    print('Expected amount of iterations to find 1 identically equal', iterAmount)
    return B, n

def getFactorBase(B):
    if B < 2:
        return []
    numbers = [True] * ((B // 2) + 1)
    numbers[0] = False
    for i in range(3, int(B**0.5)+1, 2):
        if numbers[i // 2]:
            for j in range (i*i, B + 1, 2 * i):
                numbers[j // 2] = False
    return [2] + [2 * i + 1 for i, prime in enumerate(numbers) if prime]

def checkIsBsmooth(number, B, factorBase):
    degrees = {}
    for b in factorBase:
        if b * b > number:
            break
        while number % b == 0:
            number //= b
            degrees[b] = degrees.get(b, 0) + 1
        if number == 1:
            break
    if number != 1:
        if number in factorBase:
            degrees[number] = 1
            return True, degrees
        return False, {}
    return True, degrees

def printFindX(k, degrees, p):
    print("=====find x=====")
    terms = [f"{e} * log({p})" for p, e in degrees.items()]
    expression = " + ".join(terms)
    print(f"x = {k} + {expression} (mod {p-1})")
    print("================")

def printDegrees(degrees, g, p):
    pValues = degrees.keys()
    print("=====tasks=====")
    for i, deg in enumerate(pValues):
        print(f"{g}^x{i} = {deg}(mod{p})")
    print("===============")


def printSystem(system, p):
    print("=====system=====")
    for j in system:
        terms = [f"{u} * log({p})" for p, u in system[j].items()]
        expression = " + ".join(terms)
        print(f"{j} = {expression} (mod {p-1})")
    print("================")
        

def decomposeIdention(g, h, p, B, factorBase):
    for k in range(p):
        try:
            can = ( h * pow( sympy.mod_inverse(g, p), k, p ) ) % p
        except ValueError as e:
            print(e)
            return -1
        isBsmooth, degrees = checkIsBsmooth(can, B, factorBase)
        if isBsmooth:
            printFindX(k, degrees, p)
            printDegrees(degrees, g, p)
            return degrees, k


def addDegrees(system, degrees, unused_p, j, allowed_p):
    for p, u in degrees.items():
        if(len(unused_p) > 0):
            if p in unused_p[:]:
                unused_p.remove(p)
                system[j] = degrees.copy()
        else:
            if p in allowed_p[:]:
                system[j] = degrees.copy()


def createSystem(g, p, B, necessary_p, factorBase):
    system = dict()
    unused_p = necessary_p.copy()
    allowed_p = necessary_p.copy()
    j = 2
    while True:
        if len(necessary_p) <= len(list(system.keys())) and len(unused_p) == 0: 
            break
        gj = (g ** j) % p
        if gj > 1 and gj < p:
            isBsmooth, degrees = checkIsBsmooth(gj, B, factorBase)
            if isBsmooth:
                addDegrees(system, degrees, unused_p, j, allowed_p)
                
        j += 1
    printSystem(system, p)
    return system

def getPs(degrees):
    ps = []
    for p, e in degrees:
        ps.append(p)
    return ps

def ifHasP(p, sumParts):
    for p_, u in list(sumParts.items()):
        if p == p_:
            return True, u
    return False, 0

def createMatrices(degrees, system, mod):
    only_p = getPs(list(degrees.items()))
    A_cols = []
    rightCoeffs = []
    for coef, sumParts in list(system.items()):
        rightCoeffs.append(coef)
        equation = np.zeros(len(only_p), dtype=int)
        for i, p in enumerate(only_p):
            hasP, u = ifHasP(p, sumParts)
            equation[i] = 0 if not hasP else u
        A_cols.append(list(equation.copy()))
    A_cols = [[int(x) for x  in row] for row in A_cols]
    writeMatrices(A_cols, rightCoeffs, mod)
    A = sympy.Matrix(A_cols)
    b = sympy.Matrix(rightCoeffs)
    return A, b

def printSolutions(solutions, logs, modul):
    print("=====solutions=====")
    for i, pu in enumerate(logs):
        p, _ = pu
        print(f"log({p}) = {solutions[i]} (mod {modul-1})")
    print("===================")

def writeMatrices(A, b, p):
    with open("A.txt", "w") as file:
        for row in A:
            file.write(" ".join(map(str, row))+"\n")

    with open("b.txt", "w") as file:
        file.write(" ".join(map(str, b))+"\n")

    with open("p.txt", "w") as file:
        file.write(str(p-1))


def solveSystem(g, p, degrees, system):
    A, b = createMatrices(degrees, system, p)
    with open("solve_system.sage") as f:
        code = f.read()

    result = subprocess.run(
        ["/usr/bin/sage", "-c", code],
        capture_output=True,
        text=True
    )
    lines = result.stdout.splitlines()
    solution = []
    recording = False
    for line in lines:
        if "SOLUTION_BEGIN" in line:
            recording = True
            continue
        if "SOLUTION_END" in line:
            break
        if recording:
            solution.append(int(line.strip()))
    printSolutions(solution, degrees.items(), p)
    return solution

def printX(x, p):
    print("=====found x=====")
    print(f"x = {x} mod({p-1})")
    print("=================")

def findX(k, degrees, solves, modul):
    x = k
    for i, deg in enumerate(degrees):
        p, u = deg
        x += u * solves[i]
    x %= modul - 1
    printX(x, modul)
    

if __name__=="__main__":
    g = int(input())
    h = int(input())
    p = int(input())

    c = 1/math.sqrt(2)
    B, n = preparing(p, c)
    factorBase = getFactorBase(B)
    degrees, k = decomposeIdention(g, h, p, B, factorBase)
    if degrees != -1:
        system = createSystem(g, p, B, list(degrees.keys()), factorBase)
        solves = solveSystem(g, p, degrees.copy(), system.copy())
        findX(k, degrees.items(), solves, p)
    
