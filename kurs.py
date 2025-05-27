import math
import numpy as np
import sympy
from sympy import factorint, Matrix, mod_inverse
from sympy.ntheory.modular import crt
import scipy.sparse as sp
import numpy as np
from sympy import factorint
from sympy.ntheory.modular import crt
import random
import random
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
    for k in np.arange(1, p):
        try:
            can = ( h * ((sympy.mod_inverse(g, p) ** k) ) ) % p
        except ValueError as e:
            print(e)
            return -1
        isBsmooth, degrees = checkIsBsmooth(can, B, factorBase)
        if isBsmooth:
            printFindX(k, degrees, p)
            printDegrees(degrees, g, p)
            return degrees, k


def addDegrees(system, degrees, unused_p, j, covered_set):
    new_primes = set(degrees.keys())
    if unused_p:
        if unused_p & new_primes:
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


def createSystem(g, p, B, necessary_p, factorBase, n):
    system = dict()

    unused_p = set(necessary_p)
    covered_set = set()
    j = 2

    while True:
        if len(system) >= len(factorBase) and len(unused_p) == 0: 
            break
        gj = pow(g, j, p)
        if 1 < gj < p:
            isBsmooth, degrees = checkIsBsmooth(gj, B, factorBase)
            if isBsmooth:
                if should_add_row(system, degrees, j, p-1):
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

def createMatrices(system, mod):
    all_p = sorted({p for row in system.values() for p in row})
    A_rows = []
    b_vec = []

    for j, row in system.items():
        b_vec.append(j % (mod - 1))
        A_rows.append([(row.get(p, 0)) % (mod - 1) for p in all_p])
    A = sympy.Matrix(A_rows)
    b = sympy.Matrix(b_vec)
    return A, b, all_p

def printSolutions(solutions, logs, modul, only_p: list):
    print("=====solutions=====")
    for i, pu in enumerate(logs):
        p, _ = pu
        if p in only_p:
            idx = only_p.index(p)
            print(f"log({p}) = {solutions[idx]} (mod {modul-1})")
        else:
           print(f"log({p}) = — (не найдено)")
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
        mod_x.append([ (b*mod_inverse(a % m, m)) % m for a, b in zip(a_diag, b_diag) ])
    return mod_x

def getSolutions(mod_x, mods):
    solution = []
    num_vars = len(mod_x[0]) 
    for i in range(num_vars):
        remainders = [mod_x[k][i] for k in range(len(mods))]
        x_mod_M, _ = crt(mods, remainders)   
        solution.append(int(x_mod_M % (p-1)))
    return solution


def solveSystem(g, p, pool, B, factorBase, n):
    """
    pool  – список [(deg, k), ...] из collect_smooth_k
    берём первый (deg0, k0) только для восстановления ответа,
    остальные идут в систему.
    """
    deg0, k0 = pool[0]

    # ---------- строим систему из остальных ----------
    system = { k0 : deg0.copy() }
    unused  = set(factorBase)        # ← было set(deg0)
    covered = set()            # чтобы потом убедиться, что все p_i появятся

    for deg, j in pool[1:]:
        if should_add_row(system, deg, j, p-1):
            addDegrees(system, deg, unused, j, covered)
        if not unused:               # все простые из FB уже встретили
            break

    # если после прохода ещё остались непройденные простые
    if unused:
        raise ValueError(f"Not enough relations, missing: {unused}")

    # ---------- решаем ----------
    A, b, only_p = createMatrices(system, p)
    mods = [pr**e for pr, e in factorint(p-1).items()]
    part = getPartialResults(mods, A, b)
    mod_x = getModx(part, mods)
    solution = getSolutions(mod_x, mods)

    printSolutions(solution, deg0.items(), p, only_p)
    return solution, only_p, k0, deg0


def system_complete(system: dict, factor_base: list, p_minus_1: int) -> bool:
    """
    Проверяет, что уже набрано достаточно уравнений.

    1) строк не меньше, чем |FB|;
    2) в строках встречаются **все** простые из факторной базы;
    3) по каждому простому m∣(p-1) ранг A равен |FB|.

    Возвращает True, если система «закрыта», иначе False.
    """
    # 1.  Кол-во строк
    if len(system) < len(factor_base):
        return False

    # 2.  Все ли простые из FB уже встретились?
    all_primes_in_rows = {q for row in system.values() for q in row}
    if set(factor_base) - all_primes_in_rows:
        return False

    # 3.  Ранг по каждому простому модулю
    #     (берём ту же матрицу A, что строим для решения)
    all_p = sorted(all_primes_in_rows)
    A_rows = [[row.get(q, 0) for q in all_p] for row in system.values()]
    A = Matrix(A_rows)

    for m in factorint(p_minus_1):
        if rank_modulo(A, m) < len(factor_base):
            return False

    return True


def collect_smooth_k(g,h,p,B,FB,max_rel=2_000):
    """Return a *set* of usable relations of size ≤ max_rel."""
    relations = []
    while len(relations) < max_rel:
        j = random.randrange(1, p)         # <<<<<< random, not sequential
        y = h * pow(g, -j, p) % p
        ok, deg = checkIsBsmooth(y, B, FB)
        if ok:
            relations.append((deg, j))
            if len(relations) >= len(FB) * 1.5:   # 20 % safety
                break
    return relations

def build_matrix(relations, FB, mod):
    cols = {q:i for i,q in enumerate(FB)}
    A = []
    b = []
    for deg, j in relations:
        row = [deg.get(q,0) % mod for q in FB]
        A.append(row)
        b.append(j % mod)
    return Matrix(A), Matrix(b)

def solve_for_logs(FB, relations, p):
    A, b = build_matrix(relations, FB, p-1)
    try:
        sol_vec = A.LUsolve(b)  # sympy vector of logs
    except:
        raise ValueError("Matrix not invertible — try with more relations or increase B")
    logs = [int(x % (p-1)) for x in sol_vec]
    return dict(zip(FB, logs))

def individual_log(g,h,p,FB,logs):
    k=0
    while True:
        y = h*pow(g,-k,p)%p
        ok,deg = checkIsBsmooth(y, B, FB)
        if ok:
            val = k
            for q,e in deg.items():
                val += e*logs[q]
            return val%(p-1)
        k += 1

def printX(x, p, g):
    print("=====found x=====")
    print(f"x = {x} mod({p-1})")
    print("=================")
    print("=====check x=====")
    print(f"{g}^{x} = {(g ** int(x)) % int(p)} mod({p})")
    print("=================")

def findX(k, degrees, solves, modul, only_p, g):
    x = k
    for i, p_i in enumerate(only_p):
        u = degrees.get(p_i, 0)
        x += u * solves[i]
    x %= modul - 1
    printX(x, modul, g)


def sparse_build_matrix(relations, FB, mod):
    """Строим разреженную матрицу A и вектор b"""
    row_ind, col_ind, data = [], [], []
    b = []

    prime_index = {q: i for i, q in enumerate(FB)}
    for row_idx, (deg, j) in enumerate(relations):
        b.append(j % mod)
        for prime, power in deg.items():
            if prime in prime_index:
                col = prime_index[prime]
                row_ind.append(row_idx)
                col_ind.append(col)
                data.append(power % mod)
    A = sp.csr_matrix((data, (row_ind, col_ind)), shape=(len(relations), len(FB)), dtype=int)
    b = np.array(b, dtype=np.int64)
    return A, b



def sparse_modular_gauss(A, b, mod):
    """Решаем A * x = b по модулю mod, используя scipy sparse"""
    A = A.copy().tolil()
    b = b.copy()
    n, m = A.shape

    x = np.zeros(m, dtype=int)
    row = 0
    for col in range(m):
        # найти ведущую строку
        pivot = None
        for i in range(row, n):
            if A[i, col] % mod != 0:
                pivot = i
                break
        if pivot is None:
            continue

        # меняем строки
        if pivot != row:
            A.rows[row], A.rows[pivot] = A.rows[pivot], A.rows[row]
            A.data[row], A.data[pivot] = A.data[pivot], A.data[row]
            b[row], b[pivot] = b[pivot], b[row]

        inv = pow(int(A[row, col]), -1, mod)


        # нормируем строку
        A[row, col:] = [(val * inv) % mod for val in A[row, col:].toarray().flatten()]
        b[row] = (b[row] * inv) % mod

        # зануляем всё под и над ведущим элементом
        for i in range(n):
            if i != row and A[i, col] % mod != 0:
                factor = A[i, col] % mod
                A[i, col:] = (A[i, col:].toarray().flatten() - factor * A[row, col:].toarray().flatten()) % mod
                b[i] = (b[i] - factor * b[row]) % mod
        row += 1

    # читаем решение
    for i in range(m):
        if i < n:
            x[i] = b[i]
    return x


def solve_sparse_logs(FB, relations, p):
    mods = [q**e for q, e in factorint(p - 1).items()]
    solutions = []
    for mod in mods:
        A, b = sparse_build_matrix(relations, FB, mod)
        x_mod = sparse_modular_gauss(A, b, mod)
        solutions.append(x_mod.tolist())

    # собираем решения через CRT
    num_vars = len(FB)
    final = []
    for i in range(num_vars):
        remainders = [solutions[j][i] for j in range(len(mods))]
        x_mod_M, _ = crt(mods, remainders)
        final.append(int(x_mod_M % (p - 1)))
    return dict(zip(FB, final))
    

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
    B,_ = preparing(p, 1/math.sqrt(2))
    while B < 50_000:
        FB = getFactorBase(B)
        rels = collect_smooth_k(g,h,p,B,FB)
        try:
            logs = solve_sparse_logs(FB, rels, p)
        except ValueError as e:
            print("Retrying with larger B or more relations:", e)
            B = int(B * 1.5)
            continue
        x    = individual_log(g,h,p,FB,logs)
        if pow(g,x,p)==h:
            printX(x,p,g); break
        B = int(B*1.5)
    
