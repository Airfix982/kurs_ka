import math
import numpy as np
import time
import sympy
from sympy import factorint, Matrix, mod_inverse
import random
from sympy.ntheory.modular import crt

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
    print('Expected amount of iterations to find 1 identically equal: ', iterAmount)
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
    fb = [2] + [2 * i + 1 for i, prime in enumerate(numbers) if prime]
    fb = [f for f in fb if f <= B]
    return fb

def checkIsBsmooth(number, factorBase):
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
        

def decomposeIdention(g, h, p, factorBase):
    for k in np.arange(1, p):
        try:
            can = ( h * ((sympy.mod_inverse(g, p) ** k) ) ) % p
        except ValueError as e:
            print(e)
            return -1
        isBsmooth, degrees = checkIsBsmooth(can, factorBase)
        if isBsmooth:
            printFindX(k, degrees, p)
            printDegrees(degrees, g, p)
            return degrees, k


def addDegrees(system, degrees, unused_p, j, covered_set):
    new_primes = set(degrees.keys())
    if unused_p:
        if new_primes & unused_p:
            unused_p -= new_primes
            system[j] = degrees.copy()
            covered_set.update(new_primes)
    else:
        system[j] = degrees.copy()


def rank_modulo(A, m):
    A_mod = A.applyfunc(lambda x: x % m)
    rref, _ = A_mod.rref()
    return sum(any(c % m for c in row) for row in rref.tolist())

def should_add_row(system, degrees, rhs, p_minus_1):
    primes = sorted({q for r in system.values() for q in r} | degrees.keys())
    A_rows = [[r.get(q, 0) for q in primes] for r in system.values()]
    b_vals = [[k % p_minus_1] for k in system.keys()]

    new_row = [degrees.get(q, 0) for q in primes]
    new_b   = [rhs % p_minus_1]

    A_with   = Matrix(A_rows + [new_row])
    A_no_new = Matrix(A_rows)
    Aug_with = A_with.row_join(Matrix(b_vals + [new_b]))

    n_vars = len(primes)

    for m in factorint(p_minus_1):
        if rank_modulo(A_with, m) != rank_modulo(Aug_with, m):
            return False
        if rank_modulo(A_with, m) < n_vars:
            return False
        if rank_modulo(A_with, m) == rank_modulo(A_no_new, m):
            return False
    return True

def solve_linear(a, b, m):
    a %= m
    b %= m
    g = math.gcd(a, m)
    if b % g:          # несовместимо
        return None
    a //= g
    b //= g
    m //= g
    return (b * mod_inverse(a % m, m)) % m


def createSystem(g, p, necessary_p, factorBase, n, ord_g):
    system = dict()

    unused_p = set(necessary_p)
    covered_set = set()
    j = 2

    while True:
        
        if len(system) >= len(factorBase) and len(unused_p) == 0: 
            break
        gj = pow(g, j, p)
        if 1 < gj < p:
            isBsmooth, degrees = checkIsBsmooth(gj, factorBase)
            if isBsmooth:
                if not row_is_ok(degrees, ord_g):
                    j += 1
                    continue
                if should_add_row(system, degrees, j, ord_g):
                    addDegrees(system, degrees, unused_p, j, covered_set)
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

def createMatrices(system, ord_g):
    all_p = sorted({p for row in system.values() for p in row})
    A_rows = []
    b_vec = []

    for j, row in system.items():
        b_vec.append(j % ord_g)
        A_rows.append([(row.get(p, 0)) % ord_g for p in all_p])
    A = sympy.Matrix(A_rows)
    b = sympy.Matrix(b_vec)
    return A, b, all_p

def printSolutions(solutions, logs, modul, only_p: list):
    print("=====solutions=====")
    for i, pu in enumerate(logs):
        p, _ = pu
        print(f"log({p}) = {solutions[only_p.index(p)]} (mod {modul-1})")
    print("===================")

def stairAb(A, b, p):
    n = A.rows
    m = A.cols
    for i in range(min(n, m)):
        if A[i, i] == 0:
            for r in range(i + 1, n):
                if A[r, i] != 0:
                    A.row_swap(i, r)
                    b[i], b[r] = b[r], b[i]
                    break
            else:
                continue  

        for j in range(n):
            if j == i:
                continue
            aii = A[i, i]
            aji = A[j, i]
            for k in range(m):
                A[j, k] = (A[j, k] * aii - A[i, k] * aji) % p
            b[j] = (b[j] * aii - b[i] * aji) % p

    diag = []
    b_out = []
    for i in range(min(n, m)):
        if A[i, i] != 0:
            diag.append(A[i, i])
            b_out.append(b[i] % p) 

    return diag, b_out 

def getPartialResults(mods, A, b):
    partial_results = []
    for m in mods:
        A_res, b_res = stairAb(A.copy(), b.copy(), m)
        partial_results.append((A_res, b_res))
    return partial_results

def getModx(partial_results, mods):
    mod_x = []
    for (a_diag, b_diag), m in zip(partial_results, mods):
        row = []
        for a, b in zip(a_diag, b_diag):
            x = solve_linear(a, b, m)
            if x is None:        # несовместно вся строка бракуется
                return []
            row.append(x)
        mod_x.append(row)
    return mod_x

def getSolutions(mod_x, mods, ord_g):
    solution = []
    num_vars = len(mod_x[0]) 
    for i in range(num_vars):
        remainders = [mod_x[k][i] for k in range(len(mods))]
        x_mod_M, _ = crt(mods, remainders)   
        solution.append(int(x_mod_M % ord_g))
    return solution


def row_is_ok(degrees, ord_g):
    coeffs = list(degrees.values())
    for m in (prime**exp for prime, exp in factorint(ord_g).items()):
        # общий НОД всех коэффициентов с данным m
        g = 0
        for a in coeffs:
            g = math.gcd(g, a % m)
        if g != 1:          # нет обратимых коэфф-в
            return False
    return True


def solveSystem(g, p, degrees, factorBase, n, ord_g):
    system = createSystem(g, p, list(degrees.keys()), factorBase, n, ord_g)
    A, b, only_p = createMatrices(system, ord_g)
    mods = [prime**exp for prime, exp in factorint(ord_g).items()]
    partial_results = getPartialResults(mods, A, b)

    mod_x = getModx(partial_results, mods)
    solution = getSolutions(mod_x, mods, ord_g)

    printSolutions(solution, degrees.items(), p, only_p)
    return solution, only_p


def printX(x, p, g):
    print("=====found x=====")
    print(f"x = {x} mod({p-1})")
    print("=================")
    print("=====check x=====")
    print(f"{g}^{x} = {(g ** int(x)) % int(p)} mod({p})")
    print("=================")

def findX(k, degrees, solves, modul, only_p, g, ord_g):
    x = k
    for i, p_i in enumerate(only_p):
        u = degrees.get(p_i, 0)
        x += u * solves[i]
    x %= ord_g
    printX(x, modul, g)
    

if __name__=="__main__":
    print("input g: ")
    g = int(input())
    print("input h: ")
    h = int(input())
    print("input p: ")
    p = int(input())

    ord_g = sympy.ntheory.n_order(g, p)
    if pow(h, ord_g, p) != 1:
        print("No solution exists: h is not in subgroup generated by g")
        exit()

    c = 1/math.sqrt(2)
    B, n = preparing(p, c)
    factorBase = getFactorBase(B)
    while 1:
        degrees, k = decomposeIdention(g, h, p, factorBase)
        if degrees == {}:
            printX(k, p, g)
            exit()
        if degrees != -1:
            solves, only_p = solveSystem(g, p, degrees.copy(), factorBase, n, ord_g)
            findX(k, degrees, solves, p, only_p, g, ord_g)
            exit()
    
