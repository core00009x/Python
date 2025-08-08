#!/usr/bin/env python3
# script_extremo_expanded.py
"""
Calculadora Científica Extrema - Versão Super Expandida
Inclui: análise numérica, álgebra linear, física básica, conversões, utilitários, IA, otimização e easter eggs.
Tenta usar numpy/sympy/plotext quando disponíveis; caso contrário, usa implementações próprias.
"""

import sys
import math
import cmath
import statistics
import hashlib
import shutil
import random
import time
import base64
import re
from collections import deque, Counter
from typing import List, Tuple, Dict, Any, Callable, Union

# Bibliotecas opcionais (usa se instaladas)
try:
    import numpy as np

    numpy_disponivel = True
except ImportError:
    numpy_disponivel = False

try:
    import sympy as sp

    sympy_disponivel = True
except ImportError:
    sympy_disponivel = False

try:
    import plotext as plt

    plotext_disponivel = True
except ImportError:
    plotext_disponivel = False


# --------------------
# Helpers e utilitários
# --------------------

def ler_float(prompt: str = "Digite um número: ") -> float | None:
    """Lê float com tratamento de erro; retorna None se inválido."""
    s = input(prompt).strip()
    if s == "":
        return None
    try:
        return float(s)
    except ValueError:
        print("Entrada inválida. Use um número (ex: 3.14).")
        return None


def ler_int(prompt: str = "Digite um inteiro: ") -> int | None:
    """Lê inteiro com tratamento de erro; retorna None se inválido."""
    s = input(prompt).strip()
    if s == "":
        return None
    try:
        return int(s)
    except ValueError:
        print("Entrada inválida. Use um inteiro (ex: 42).")
        return None


def pergunta_sim_nao(prompt: str) -> bool:
    """Faz uma pergunta de sim/não."""
    r = input(prompt + " (s/n): ").strip().lower()
    return r.startswith('s')


def clear_console():
    """Limpa a tela do console."""
    try:
        import os
        os.system('cls' if os.name == 'nt' else 'clear')
    except Exception:
        pass


# --------------------
# Funções matemáticas extras
# --------------------

def derivada_numerica(f: Callable[[float], float], x: float, h: float = 1e-6) -> float:
    """Calcula a derivada numérica de f em x usando diferenças finitas centrais."""
    return (f(x + h) - f(x - h)) / (2 * h)


def metodo_bisseccao(f: Callable[[float], float], a: float, b: float, tol: float = 1e-8, max_iter: int = 100) -> Tuple[
    float, int]:
    """Método da bissecção para encontrar raiz de f entre [a,b]."""
    fa = f(a);
    fb = f(b)
    if fa * fb > 0:
        raise ValueError("f(a) e f(b) devem ter sinais opostos.")
    for i in range(max_iter):
        c = (a + b) / 2.0
        fc = f(c)
        if abs(fc) < tol or (b - a) / 2 < tol:
            return c, i + 1
        if fa * fc <= 0:
            b = c
            fb = fc
        else:
            a = c
            fa = fc
    return (a + b) / 2.0, max_iter


def metodo_newton(f: Callable[[float], float], df: Callable[[float], float], x0: float, tol: float = 1e-10,
                  max_iter: int = 100) -> Tuple[float, int]:
    """Método de Newton-Raphson com retorno de (raiz, iterações)."""
    x = x0
    for i in range(max_iter):
        fx = f(x)
        dfx = df(x)
        if dfx == 0:
            raise ZeroDivisionError("Derivada zero; escolha outro x0.")
        x_next = x - fx / dfx
        if abs(x_next - x) < tol:
            return x_next, i + 1
        x = x_next
    return x, max_iter


def integral_trapezio(f: Callable[[float], float], a: float, b: float, n: int = 1000) -> float:
    """Integral numérica pelo método do trapézio."""
    if n < 1: n = 1
    h = (b - a) / n
    s = 0.5 * (f(a) + f(b))
    for k in range(1, n):
        s += f(a + k * h)
    return s * h


def integral_simpson(f: Callable[[float], float], a: float, b: float, n: int = 1000) -> float:
    """Integral numérica por Simpson (n deve ser par)."""
    if n % 2 == 1: n += 1
    h = (b - a) / n
    s = f(a) + f(b)
    for k in range(1, n):
        coef = 4 if k % 2 == 1 else 2
        s += coef * f(a + k * h)
    return s * h / 3


def crivo_eratostenes(n: int) -> List[int]:
    """Gera lista de primos até n (inclusive)."""
    if n < 2: return []
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    p = 2
    while p * p <= n:
        if sieve[p]:
            for multiple in range(p * p, n + 1, p):
                sieve[multiple] = False
        p += 1
    return [i for i, prime in enumerate(sieve) if prime]


def fatoracao(n: int) -> Dict[int, int]:
    """Retorna fatoração prima como dicionário {p:exp}."""
    if n == 0: return {0: 1}
    n = abs(int(n))
    res = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            res[d] = res.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        res[n] = res.get(n, 0) + 1
    return res


def fibonacci_n(n: int) -> int:
    """Calcula o n-ésimo número de Fibonacci."""
    if n < 0: raise ValueError("n deve ser >= 0")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def euler_totient(n: int) -> int:
    """Calcula a função totiente de Euler phi(n)."""
    if not isinstance(n, int) or n <= 0: raise ValueError("n deve ser um inteiro positivo.")
    result = n
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0: n //= p
            result -= result // p
        p += 1
    if n > 1: result -= result // n
    return result


def modular_exponentiation(base: int, exp: int, mod: int) -> int:
    """Calcula (base^exp) % mod de forma eficiente."""
    return pow(base, exp, mod)


def gcd(a: int, b: int) -> int:
    """Calcula o Máximo Divisor Comum (MDC) usando o Algoritmo de Euclides."""
    while b:
        a, b = b, a % b
    return a


def extended_gcd(a: int, b: int) -> Tuple[int, int, int]:
    """Calcula o MDC e os coeficientes de Bézout (ax + by = mdc)."""
    if a == 0:
        return b, 0, 1
    d, x1, y1 = extended_gcd(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return d, x, y


def polynomial_roots():
    """Encontra raízes de um polinômio."""
    print("Digite os coeficientes do polinômio, do mais alto ao mais baixo. Ex: 1 -3 2 para x^2 - 3x + 2")
    s_coeffs = input("Coeficientes separados por espaço: ").strip().split()
    try:
        coeffs = [float(c) for c in s_coeffs]
    except ValueError:
        print("Entrada inválida. Use apenas números.")
        return
    if not coeffs:
        print("Nenhum coeficiente digitado.")
        return

    if numpy_disponivel:
        try:
            roots = np.roots(coeffs)
            print("Raízes:")
            for root in roots:
                if abs(root.imag) < 1e-12:
                    print(f"  {root.real:.6g}")
                else:
                    print(f"  {root:.6g}")
        except Exception as e:
            print(f"Erro ao calcular as raízes: {e}")
    else:
        print("numpy não disponível. Não é possível calcular raízes de forma geral.")
        if len(coeffs) == 3:
            a, b, c = coeffs
            delta = b ** 2 - 4 * a * c
            if delta >= 0:
                print(
                    f"Raízes (fórmula de Bhaskara): {(-b + math.sqrt(delta)) / (2 * a):.6g} e {(-b - math.sqrt(delta)) / (2 * a):.6g}")
            else:
                print(
                    f"Raízes (fórmula de Bhaskara): {(-b + cmath.sqrt(delta)) / (2 * a):.6g} e {(-b - cmath.sqrt(delta)) / (2 * a):.6g}")


# --------------------
# Álgebra linear (usa numpy se disponível)
# --------------------

def matriz_from_input() -> Union['np.ndarray', List[List[float]], None]:
    """Lê matriz linhas por linha com números separados por espaço."""
    print("Digite a matriz linha a linha. Linha vazia para terminar.")
    rows = []
    while True:
        line = input().strip()
        if line == "":
            break
        vals = line.split()
        try:
            row = [float(v) for v in vals]
            rows.append(row)
        except ValueError:
            print("Linha inválida. Use números separados por espaço.")
    if not rows: return None
    ncols = len(rows[0])
    for r in rows:
        if len(r) != ncols:
            print("Todas as linhas devem ter o mesmo número de colunas.")
            return None
    return np.array(rows, dtype=float) if numpy_disponivel else rows


def vetor_from_input() -> Union['np.ndarray', List[float], None]:
    """Lê vetor a partir de uma linha de números separados por espaço."""
    s = input("Digite o vetor (números separados por espaço): ")
    try:
        vec = [float(v) for v in s.split()]
        return np.array(vec, dtype=float) if numpy_disponivel else vec
    except ValueError:
        print("Entrada inválida. Use números separados por espaço.")
        return None


def soma_matrizes(A: Any, B: Any) -> Any:
    if numpy_disponivel:
        return A + B
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def multiplicacao_matrizes(A: Any, B: Any) -> Any:
    if numpy_disponivel:
        return A.dot(B)
    if len(A[0]) != len(B):
        raise ValueError("Número de colunas de A deve ser igual ao número de linhas de B.")
    n, m, p = len(A), len(A[0]), len(B[0])
    C = [[0.0 for _ in range(p)] for _ in range(n)]
    for i in range(n):
        for j in range(p):
            for k in range(m):
                C[i][j] += A[i][k] * B[k][j]
    return C


def determinante(A: Any) -> float:
    if numpy_disponivel:
        return float(np.linalg.det(A))
    n = len(A)
    if n != len(A[0]):
        raise ValueError("Matriz não quadrada.")
    if n == 1: return A[0][0]
    if n == 2: return A[0][0] * A[1][1] - A[0][1] * A[1][0]
    total = 0
    for col in range(n):
        sub = [row[:col] + row[col + 1:] for row in A[1:]]
        sign = (-1) ** col
        total += sign * A[0][col] * determinante(sub)
    return total


def inversa(A: Any) -> Any:
    if numpy_disponivel:
        return np.linalg.inv(A)
    n = len(A)
    if n != len(A[0]):
        raise ValueError("Matriz não quadrada.")
    M = [list(map(float, row)) + [1.0 if i == j else 0.0 for j in range(n)] for i, row in enumerate(A)]
    for i in range(n):
        pivot = M[i][i]
        if abs(pivot) < 1e-12:
            for r in range(i + 1, n):
                if abs(M[r][i]) > 1e-12:
                    M[i], M[r] = M[r], M[i]
                    pivot = M[i][i]
                    break
        if abs(pivot) < 1e-12: raise ValueError("Matriz singular")
        for j in range(2 * n): M[i][j] /= pivot
        for r in range(n):
            if r != i:
                fac = M[r][i]
                for j in range(2 * n): M[r][j] -= fac * M[i][j]
    inv = [row[n:] for row in M]
    return inv


def matriz_transposta(A: Any) -> Any:
    if numpy_disponivel:
        return A.T
    if not A or not A[0]: return []
    rows, cols = len(A), len(A[0])
    return [[A[j][i] for j in range(rows)] for i in range(cols)]


def eigen_values_vectors(A: Any):
    if numpy_disponivel:
        try:
            w, v = np.linalg.eig(A)
            print("Autovalores:");
            print(w)
            print("\nAutovetores (colunas):");
            print(v)
        except Exception as e:
            print(f"Erro: {e}")
    else:
        print("numpy não disponível. Não é possível calcular autovalores/autovetores sem numpy.")


def solve_linear_system(A: Any, b: Any):
    if numpy_disponivel:
        try:
            x = np.linalg.solve(A, b)
            print("Solução x:");
            print(x)
        except Exception as e:
            print(f"Erro: {e}")
    else:
        print("numpy não disponível. Não é possível resolver sistemas lineares sem numpy.")


def decomposicao_lu(A: Any) -> Tuple[Any, Any]:
    if numpy_disponivel:
        from scipy.linalg import lu
        P, L, U = lu(A)
        print("Decomposição LU (com pivoting)")
        print("Matriz P (permutação):\n", P)
        print("Matriz L (inferior):\n", L)
        print("Matriz U (superior):\n", U)
        return L, U
    n = len(A)
    if n != len(A[0]): raise ValueError("Matriz não quadrada.")
    L = [[0.0 for _ in range(n)] for _ in range(n)]
    U = [row[:] for row in A]
    for j in range(n):
        L[j][j] = 1.0
        if abs(U[j][j]) < 1e-12:
            raise ValueError("Não é possível decompor LU sem pivoting.")
        for i in range(j + 1, n):
            factor = U[i][j] / U[j][j]
            L[i][j] = factor
            for k in range(j, n):
                U[i][k] -= factor * U[j][k]
    return L, U


def decomposicao_qr(A: Any) -> Tuple[Any, Any]:
    if numpy_disponivel:
        Q, R = np.linalg.qr(A)
        return Q, R
    m, n = len(A), len(A[0])
    if m < n: raise ValueError("Matriz A deve ter mais ou o mesmo número de linhas que de colunas.")
    Q = [[0.0 for _ in range(n)] for _ in range(m)]
    R = [[0.0 for _ in range(n)] for _ in range(n)]
    V = [row[:] for row in A]
    for j in range(n):
        vj = [V[i][j] for i in range(m)]
        mag_vj_sq = sum(x ** 2 for x in vj)
        R[j][j] = math.sqrt(mag_vj_sq)
        for i in range(m): Q[i][j] = vj[i] / R[j][j]
        for k in range(j + 1, n):
            vk = [V[i][k] for i in range(m)]
            R[j][k] = sum(Q[i][j] * vk[i] for i in range(m))
            for i in range(m): V[i][k] -= R[j][k] * Q[i][j]
    return Q, R


def matriz_covariancia(dados: Any) -> Any:
    if numpy_disponivel:
        return np.cov(dados, rowvar=False)

    if not isinstance(dados, list) or not dados or not isinstance(dados[0], list):
        raise ValueError("Dados devem ser uma lista de listas (amostras por coluna).")

    m, n = len(dados), len(dados[0])
    if m < 2:
        raise ValueError("É necessário pelo menos duas amostras para calcular a covariância.")

    dados_t = [[dados[j][i] for j in range(m)] for i in range(n)]
    medias = [sum(col) / m for col in dados_t]

    cov_matrix = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            soma = 0.0
            for k in range(m):
                soma += (dados[k][i] - medias[i]) * (dados[k][j] - medias[j])
            cov_matrix[i][j] = soma / (m - 1)
    return cov_matrix


def matriz_vandermonde(v: List[float], n: int = None) -> Any:
    if numpy_disponivel:
        return np.vander(v, N=n)
    if n is None: n = len(v)
    m = len(v)
    if n <= 0 or m <= 0: raise ValueError("Dimensões devem ser positivas.")
    matrix = [[0.0 for _ in range(n)] for _ in range(m)]
    for i in range(m):
        for j in range(n):
            matrix[i][j] = v[i] ** (n - 1 - j)
    return matrix


# --------------------
# Geometria e Cálculo Vetorial
# --------------------

def geometria_solidos():
    """Calcula a área e o volume de sólidos geométricos comuns."""
    print("\n--- GEOMETRIA DE SÓLIDOS ---")
    print("a) Esfera\nb) Cubo\nc) Cilindro\nd) Cone\n0) Voltar")
    op = input("Escolha: ").strip().lower()

    try:
        if op == 'a':
            r = ler_float("Raio (r): ")
            if r is None or r < 0: return
            area = 4 * math.pi * r ** 2
            volume = (4 / 3) * math.pi * r ** 3
            print(f"Área da superfície = {area:.6g}")
            print(f"Volume = {volume:.6g}")
        elif op == 'b':
            l = ler_float("Lado (l): ")
            if l is None or l < 0: return
            area = 6 * l ** 2
            volume = l ** 3
            print(f"Área da superfície = {area:.6g}")
            print(f"Volume = {volume:.6g}")
        elif op == 'c':
            r = ler_float("Raio (r): ")
            h = ler_float("Altura (h): ")
            if None in (r, h) or r < 0 or h < 0: return
            area_base = math.pi * r ** 2
            area_lateral = 2 * math.pi * r * h
            area_total = 2 * area_base + area_lateral
            volume = area_base * h
            print(f"Área da superfície = {area_total:.6g}")
            print(f"Volume = {volume:.6g}")
        elif op == 'd':
            r = ler_float("Raio (r): ")
            h = ler_float("Altura (h): ")
            if None in (r, h) or r < 0 or h < 0: return
            sl = math.sqrt(r ** 2 + h ** 2)
            area_base = math.pi * r ** 2
            area_lateral = math.pi * r * sl
            area_total = area_base + area_lateral
            volume = (1 / 3) * area_base * h
            print(f"Área da superfície = {area_total:.6g}")
            print(f"Volume = {volume:.6g}")
        elif op == '0':
            return
        else:
            print("Opção inválida.")
    except Exception as e:
        print(f"Erro: {e}")


def distancia_pontos():
    """Calcula a distância entre dois pontos em 2D ou 3D."""
    print("a) 2D\nb) 3D")
    dim = input("Dimensões: ").strip().lower()
    try:
        if dim == 'a':
            x1 = ler_float("x1: ");
            y1 = ler_float("y1: ")
            x2 = ler_float("x2: ");
            y2 = ler_float("y2: ")
            if None in (x1, y1, x2, y2): return
            dist = math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)
            print(f"Distância = {dist:.6g}")
        elif dim == 'b':
            x1 = ler_float("x1: ");
            y1 = ler_float("y1: ");
            z1 = ler_float("z1: ")
            x2 = ler_float("x2: ");
            y2 = ler_float("y2: ");
            z2 = ler_float("z2: ")
            if None in (x1, y1, z1, x2, y2, z2): return
            dist = math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2 + (z2 - z1) ** 2)
            print(f"Distância = {dist:.6g}")
        else:
            print("Opção inválida.")
    except Exception as e:
        print(f"Erro: {e}")


def operacoes_vetoriais():
    """Calcula produto escalar, produto vetorial e projeção de vetores."""
    print("\n--- OPERAÇÕES VETORIAIS ---")
    print("a) Produto Escalar (Dot Product)\nb) Produto Vetorial (Cross Product)\nc) Projeção de Vetores\n0) Voltar")
    op = input("Escolha: ").strip().lower()

    def ler_vetor3d(prompt):
        s = input(f"{prompt} (ex: 1 2 3): ").strip().split()
        if len(s) != 3:
            print("Entrada inválida. Digite 3 números.")
            return None
        try:
            return [float(v) for v in s]
        except ValueError:
            print("Entrada inválida. Use apenas números.")
            return None

    try:
        if op == 'a':
            v1 = ler_vetor3d("Vetor 1");
            v2 = ler_vetor3d("Vetor 2")
            if None in (v1, v2): return
            res = sum(x * y for x, y in zip(v1, v2))
            print(f"Produto Escalar = {res:.6g}")
        elif op == 'b':
            v1 = ler_vetor3d("Vetor 1");
            v2 = ler_vetor3d("Vetor 2")
            if None in (v1, v2): return
            res = [v1[1] * v2[2] - v1[2] * v2[1],
                   v1[2] * v2[0] - v1[0] * v2[2],
                   v1[0] * v2[1] - v1[1] * v2[0]]
            print(f"Produto Vetorial = ({res[0]:.6g}, {res[1]:.6g}, {res[2]:.6g})")
        elif op == 'c':
            v1 = ler_vetor3d("Vetor a projetar");
            v2 = ler_vetor3d("Vetor de projeção")
            if None in (v1, v2): return
            dot_prod = sum(x * y for x, y in zip(v1, v2))
            mag_sq_v2 = sum(x ** 2 for x in v2)
            if mag_sq_v2 == 0:
                print("Vetor de projeção não pode ser zero.")
                return
            scalar = dot_prod / mag_sq_v2
            res = [scalar * x for x in v2]
            print(f"Projeção = ({res[0]:.6g}, {res[1]:.6g}, {res[2]:.6g})")
        elif op == '0':
            return
        else:
            print("Opção inválida.")
    except Exception as e:
        print(f"Erro: {e}")


def rotacao_vetores():
    """Gira um vetor em 2D ou 3D."""
    print("a) Rotação 2D\nb) Rotação 3D (Eixos X, Y, Z)\n0) Voltar")
    op = input("Escolha: ").strip().lower()

    try:
        if op == 'a':
            x, y = ler_float("x: "), ler_float("y: ")
            angulo_graus = ler_float("Ângulo (graus): ")
            if None in (x, y, angulo_graus): return
            angulo_rad = math.radians(angulo_graus)
            x_novo = x * math.cos(angulo_rad) - y * math.sin(angulo_rad)
            y_novo = x * math.sin(angulo_rad) + y * math.cos(angulo_rad)
            print(f"Vetor rotacionado: ({x_novo:.6g}, {y_novo:.6g})")
        elif op == 'b':
            x, y, z = ler_float("x: "), ler_float("y: "), ler_float("z: ")
            angulo_graus = ler_float("Ângulo (graus): ")
            eixo = input("Eixo de rotação (x, y, z): ").strip().lower()
            if None in (x, y, z, angulo_graus) or eixo not in ['x', 'y', 'z']: return
            angulo_rad = math.radians(angulo_graus)
            cos_a, sin_a = math.cos(angulo_rad), math.sin(angulo_rad)

            x_novo, y_novo, z_novo = x, y, z
            if eixo == 'x':
                y_novo = y * cos_a - z * sin_a
                z_novo = y * sin_a + z * cos_a
            elif eixo == 'y':
                x_novo = x * cos_a + z * sin_a
                z_novo = -x * sin_a + z * cos_a
            elif eixo == 'z':
                x_novo = x * cos_a - y * sin_a
                y_novo = x * sin_a + y * cos_a

            print(f"Vetor rotacionado: ({x_novo:.6g}, {y_novo:.6g}, {z_novo:.6g})")
        elif op == '0':
            return
        else:
            print("Opção inválida.")
    except Exception as e:
        print(f"Erro: {e}")


# --------------------
# Física básica e Engenharia
# --------------------

def mru(s0: float | None = None, v: float | None = None, t: float | None = None):
    """MRU: s = s0 + v*t"""
    s0 = s0 if s0 is not None else ler_float("Posição inicial s0: ")
    v = v if v is not None else ler_float("Velocidade v: ")
    t = t if t is not None else ler_float("Tempo t: ")
    if None in (s0, v, t): print("Parâmetro(s) faltando."); return
    s = s0 + v * t
    print(f"Posição final: s = {s}")


def mruv(s0: float | None = None, v0: float | None = None, a: float | None = None, t: float | None = None):
    """MRUV: s = s0 + v0*t + 0.5*a*t^2 ; v = v0 + a*t"""
    s0 = s0 if s0 is not None else ler_float("Posição inicial s0: ")
    v0 = v0 if v0 is not None else ler_float("Velocidade inicial v0: ")
    a = a if a is not None else ler_float("Aceleração a: ")
    t = t if t is not None else ler_float("Tempo t: ")
    if None in (s0, v0, a, t): print("Parâmetro(s) faltando."); return
    s = s0 + v0 * t + 0.5 * a * t * t
    v = v0 + a * t
    print(f"Posição final: s = {s}")
    print(f"Velocidade final: v = {v}")


def lancamento_obliquo(v0: float | None = None, ang_graus: float | None = None, g: float = 9.80665):
    """Dados v0 e ângulo, calcula alcance, tempo de voo e altura máxima."""
    v0 = v0 if v0 is not None else ler_float("Velocidade inicial v0 (m/s): ")
    ang_graus = ang_graus if ang_graus is not None else ler_float("Ângulo de lançamento (graus): ")
    if None in (v0, ang_graus): print("Parâmetro(s) faltando."); return
    th = math.radians(ang_graus)
    t_voo = 2 * v0 * math.sin(th) / g
    alcance = v0 * math.cos(th) * t_voo
    h_max = (v0 ** 2) * (math.sin(th) ** 2) / (2 * g)
    print(f"Tempo de voo: {t_voo:.6g} s")
    print(f"Alcance horizontal: {alcance:.6g} m")
    print(f"Altura máxima: {h_max:.6g} m")


def lei_de_ohm():
    print("Qual variável você quer calcular?")
    print("a) Voltagem (V)\nb) Corrente (I)\nc) Resistência (R)")
    op = input("Escolha: ").strip().lower()
    try:
        if op == 'a':
            i = ler_float("Corrente (I): ");
            r = ler_float("Resistência (R): ")
            print(f"V = {i * r:.6g} V")
        elif op == 'b':
            v = ler_float("Voltagem (V): ");
            r = ler_float("Resistência (R): ")
            if r == 0:
                print("Resistência não pode ser zero.")
            else:
                print(f"I = {v / r:.6g} A")
        elif op == 'c':
            v = ler_float("Voltagem (V): ");
            i = ler_float("Corrente (I): ")
            if i == 0:
                print("Corrente não pode ser zero.")
            else:
                print(f"R = {v / i:.6g} Ω")
        else:
            print("Opção inválida.")
    except TypeError:
        print("Entrada inválida.")


def energia_cinetica():
    try:
        m = ler_float("Massa (m): ");
        v = ler_float("Velocidade (v): ")
        if None in (m, v): return
        ke = 0.5 * m * v ** 2
        print(f"Energia Cinética = {ke:.6g} J")
    except TypeError:
        print("Entrada inválida.")


def lei_dos_gases_ideais():
    print("Lei dos Gases Ideais: PV = nRT")
    print("Qual variável você quer calcular?")
    print("a) Pressão (P)\nb) Volume (V)\nc) Quantidade de matéria (n)\nd) Temperatura (T)")
    op = input("Escolha: ").strip().lower()
    R = 8.314462618
    try:
        if op == 'a':
            v = ler_float("Volume (V, m^3): ");
            n = ler_float("Quantidade (n, mol): ");
            t = ler_float("Temperatura (T, K): ")
            if v == 0:
                print("Volume não pode ser zero.")
            else:
                print(f"P = {(n * R * t) / v:.6g} Pa")
        elif op == 'b':
            p = ler_float("Pressão (P, Pa): ");
            n = ler_float("Quantidade (n, mol): ");
            t = ler_float("Temperatura (T, K): ")
            if p == 0:
                print("Pressão não pode ser zero.")
            else:
                print(f"V = {(n * R * t) / p:.6g} m^3")
        elif op == 'c':
            p = ler_float("Pressão (P, Pa): ");
            v = ler_float("Volume (V, m^3): ");
            t = ler_float("Temperatura (T, K): ")
            if t == 0:
                print("Temperatura não pode ser zero.")
            else:
                print(f"n = {(p * v) / (R * t):.6g} mol")
        elif op == 'd':
            p = ler_float("Pressão (P, Pa): ");
            v = ler_float("Volume (V, m^3): ");
            n = ler_int("Quantidade (n, mol): ")
            if n == 0:
                print("Quantidade de matéria não pode ser zero.")
            else:
                print(f"T = {(p * v) / (R * n):.6g} K")
        else:
            print("Opção inválida.")
    except TypeError:
        print("Entrada inválida.")


def gravitacao_universal():
    G = 6.67430e-11
    try:
        m1 = ler_float("Massa do corpo 1 (kg): ");
        m2 = ler_float("Massa do corpo 2 (kg): ")
        r = ler_float("Distância entre os centros (m): ")
        if None in (m1, m2, r): return
        if r == 0:
            print("Distância não pode ser zero.")
        else:
            f = (G * m1 * m2) / r ** 2
            print(f"Força gravitacional (F) = {f:.6g} N")
    except TypeError:
        print("Entrada inválida.")


# --------------------
# Conversões científicas
# --------------------

CONSTANTES = {
    'pi': math.pi, 'e': math.e, 'phi': (1 + math.sqrt(5)) / 2, 'c': 299792458,
    'G': 6.67430e-11, 'h': 6.62607015e-34, 'kB': 1.380649e-23, 'NA': 6.02214076e23
}


def conversao_temperatura():
    print("a) C -> F\nb) F -> C\nc) C -> K\nd) K -> C")
    op = input("Escolha: ").strip().lower()
    if op == 'a':
        c = ler_float("°C: ");
        print(f"{c} °C = {c * 9 / 5 + 32} °F")
    elif op == 'b':
        f = ler_float("°F: ");
        print(f"{f} °F = {(f - 32) * 5 / 9} °C")
    elif op == 'c':
        c = ler_float("°C: ");
        print(f"{c} °C = {c + 273.15} K")
    elif op == 'd':
        k = ler_float("K: ");
        print(f"{k} K = {k - 273.15} °C")
    else:
        print("Opção inválida.")


def conversao_velocidade():
    print("a) m/s -> km/h\nb) km/h -> m/s\nc) m/s -> mph\nd) mph -> m/s")
    op = input("Escolha: ").strip().lower()
    if op == 'a':
        v = ler_float("m/s: ");
        print(f"{v} m/s = {v * 3.6} km/h")
    elif op == 'b':
        v = ler_float("km/h: ");
        print(f"{v} km/h = {v / 3.6} m/s")
    elif op == 'c':
        v = ler_float("m/s: ");
        print(f"{v} m/s = {v * 2.2369362920544} mph")
    elif op == 'd':
        v = ler_float("mph: ");
        print(f"{v} mph = {v / 2.2369362920544} m/s")
    else:
        print("Opção inválida.")


def romanos_para_arabicos():
    roman_map = {'I': 1, 'V': 5, 'X': 10, 'L': 50, 'C': 100, 'D': 500, 'M': 1000}
    s = input("Digite um numeral romano: ").strip().upper()
    total, prev_val = 0, 0
    try:
        for c in reversed(s):
            val = roman_map[c]
            total += val if val >= prev_val else -val
            prev_val = val
        print(f"O numeral arábico é: {total}")
    except KeyError:
        print("Entrada inválida. Use apenas I, V, X, L, C, D, M.")


def arabicos_para_romanos():
    val = ler_int("Digite um número arábico (1 a 3999): ")
    if val is None or not (1 <= val <= 3999):
        print("Número inválido.");
        return
    romans = [(1000, 'M'), (900, 'CM'), (500, 'D'), (400, 'CD'), (100, 'C'),
              (90, 'XC'), (50, 'L'), (40, 'XL'), (10, 'X'), (9, 'IX'),
              (5, 'V'), (4, 'IV'), (1, 'I')]
    result = ""
    for arabic, roman in romans:
        while val >= arabic:
            result += roman
            val -= arabic
    print(f"O numeral romano é: {result}")


def base64_converter():
    print("a) Codificar (Encode)\nb) Decodificar (Decode)")
    op = input("Escolha: ").strip().lower()
    if op == 'a':
        s = input("Digite o texto a codificar: ").encode('utf-8')
        encoded = base64.b64encode(s)
        print("Resultado:", encoded.decode('utf-8'))
    elif op == 'b':
        s = input("Digite o texto a decodificar: ").encode('utf-8')
        try:
            decoded = base64.b64decode(s)
            print("Resultado:", decoded.decode('utf-8'))
        except Exception as e:
            print(f"Erro ao decodificar: {e}")
    else:
        print("Opção inválida.")


# --------------------
# Estatística e probabilidade
# --------------------

def normal_pdf(x: float, mu: float = 0, sigma: float = 1) -> float:
    u = (x - mu) / sigma
    return (1.0 / (math.sqrt(2 * math.pi) * sigma)) * math.exp(-u * u / 2)


def normal_cdf(x: float, mu: float = 0, sigma: float = 1) -> float:
    return 0.5 * (1 + math.erf((x - mu) / (sigma * math.sqrt(2))))


def distribuicao_binomial_pmf(k: int, n: int, p: float) -> float:
    from math import comb
    return comb(n, k) * (p ** k) * ((1 - p) ** (n - k))


def distribuicao_poisson_pmf(k: int, lam: float) -> float:
    return math.exp(-lam) * (lam ** k) / math.factorial(k)


def regressao_linear_simples():
    print("Regressão Linear Simples: y = ax + b")
    print("Digite os valores de X separados por espaço:")
    try:
        x_vals = list(map(float, input().split()))
        print("Digite os valores de Y separados por espaço:")
        y_vals = list(map(float, input().split()))
        if len(x_vals) != len(y_vals) or len(x_vals) < 2:
            print("As listas devem ter o mesmo tamanho e ter pelo menos 2 pontos.");
            return

        n = len(x_vals)
        sum_x = sum(x_vals);
        sum_y = sum(y_vals)
        sum_xy = sum(x * y for x, y in zip(x_vals, y_vals))
        sum_x2 = sum(x ** 2 for x in x_vals)

        a = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x ** 2)
        b = (sum_y / n) - a * (sum_x / n)
        y_mean = sum_y / n
        ss_total = sum((y - y_mean) ** 2 for y in y_vals)
        ss_residual = sum((y - (a * x + b)) ** 2 for x, y in zip(x_vals, y_vals))
        r_squared = 1 - (ss_residual / ss_total) if ss_total != 0 else 1

        print(f"Equação: y = {a:.6g}x + {b:.6g}")
        print(f"Coeficiente de determinação (R^2): {r_squared:.6g}")
    except Exception as e:
        print(f"Erro: {e}")


def coeficiente_correlacao():
    print("Cálculo do Coeficiente de Correlação de Pearson")
    print("Digite os valores de X separados por espaço:")
    try:
        x_vals = list(map(float, input().split()))
        print("Digite os valores de Y separados por espaço:")
        y_vals = list(map(float, input().split()))
        if len(x_vals) != len(y_vals) or len(x_vals) < 2:
            print("As listas devem ter o mesmo tamanho e ter pelo menos 2 pontos.");
            return

        if numpy_disponivel:
            corr = np.corrcoef(x_vals, y_vals)[0, 1]
            print(f"Coeficiente de correlação (r): {corr:.6g}")
        else:
            n = len(x_vals);
            mean_x = statistics.mean(x_vals);
            mean_y = statistics.mean(y_vals)
            cov = sum((x - mean_x) * (y - mean_y) for x, y in zip(x_vals, y_vals))
            stdev_x = math.sqrt(sum((x - mean_x) ** 2 for x in x_vals))
            stdev_y = math.sqrt(sum((y - mean_y) ** 2 for y in y_vals))
            if stdev_x * stdev_y == 0:
                print("Não foi possível calcular o coeficiente de correlação (desvio padrão zero).")
            else:
                corr = cov / (stdev_x * stdev_y)
                print(f"Coeficiente de correlação (r): {corr:.6g}")
    except Exception as e:
        print(f"Erro: {e}")


# --------------------
# Utilitários de programação
# --------------------

class Stack:
    """Implementação básica de uma pilha (LIFO)."""

    def __init__(self): self._list: List[Any] = []

    def push(self, item: Any): self._list.append(item)

    def pop(self) -> Any | None: return self._list.pop() if self._list else None

    def peek(self) -> Any | None: return self._list[-1] if self._list else None

    def is_empty(self) -> bool: return not self._list

    def __repr__(self) -> str: return f"Pilha: {self._list}"


class Queue:
    """Implementação básica de uma fila (FIFO)."""

    def __init__(self): self._deque: deque[Any] = deque()

    def enqueue(self, item: Any): self._deque.append(item)

    def dequeue(self) -> Any | None: return self._deque.popleft() if self._deque else None

    def peek(self) -> Any | None: return self._deque[0] if self._deque else None

    def is_empty(self) -> bool: return not self._deque

    def __repr__(self) -> str: return f"Fila: {list(self._deque)}"


def menu_estruturas_dados():
    stack = Stack();
    queue = Queue()
    print("Escolha a estrutura: a) Pilha b) Fila")
    op = input().strip().lower()
    ds = stack if op == 'a' else queue
    while True:
        print(f"\n{ds}")
        print("1. Adicionar 2. Remover 3. Ver topo/frente 4. Voltar")
        sub_op = input("Escolha: ").strip()
        if sub_op == '1':
            item = input("Item a adicionar: ")
            ds.push(item) if op == 'a' else ds.enqueue(item)
        elif sub_op == '2':
            item = ds.pop() if op == 'a' else ds.dequeue()
            print(f"Removido: {item}")
        elif sub_op == '3':
            item = ds.peek()
            print(f"Topo/Frente: {item}")
        elif sub_op == '4':
            break
        else:
            print("Opção inválida.")


def texto_para_ascii():
    s = input("Digite o texto: ")
    codes = [str(ord(c)) for c in s]
    print("Códigos ASCII / Unicode:", " ".join(codes))


def conversao_base():
    n = input("Número (inteiro) a converter: ").strip()
    try:
        base_from = int(input("Base de entrada (2-36): "))
        base_to = int(input("Base de saída (2-36): "))
    except ValueError:
        print("Base inválida."); return
    try:
        value = int(n, base_from)
    except ValueError:
        print("Número inválido na base informada."); return
    digits = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    if value == 0: print("0"); return
    out = ""
    v = value
    while v > 0:
        out = digits[v % base_to] + out
        v //= base_to
    print(f"{n} (base {base_from}) = {out} (base {base_to})")


def gerar_hash():
    s = input("Texto para hashear: ").encode('utf-8')
    print("MD5:", hashlib.md5(s).hexdigest())
    print("SHA1:", hashlib.sha1(s).hexdigest())
    print("SHA256:", hashlib.sha256(s).hexdigest())


def cifra_cesar():
    txt = input("Texto: ")
    k = ler_int("Deslocamento (ex: 3): ")
    if k is None: return
    res = []
    for ch in txt:
        if ch.isalpha():
            base = 'A' if ch.isupper() else 'a'
            res.append(chr((ord(ch) - ord(base) + k) % 26 + ord(base)))
        else:
            res.append(ch)
    print("Resultado:", "".join(res))


def cifra_vigenere():
    txt = input("Texto (apenas letras): ").upper().replace(" ", "")
    key = input("Chave (apenas letras): ").upper().replace(" ", "")
    if not txt or not key or not txt.isalpha() or not key.isalpha():
        print("Entrada inválida. Use apenas letras.");
        return
    op = input("a) Criptografar b) Descriptografar: ").strip().lower()
    res = []
    key_len = len(key)
    for i, char in enumerate(txt):
        key_char = key[i % key_len]
        key_shift = ord(key_char) - ord('A')
        if op == 'b': key_shift = -key_shift
        new_char_code = (ord(char) - ord('A') + key_shift) % 26 + ord('A')
        res.append(chr(new_char_code))
    print("Resultado:", "".join(res))


def rle_converter():
    print("a) Codificar (Encode)\nb) Decodificar (Decode)")
    op = input("Escolha: ").strip().lower()
    if op == 'a':
        s = input("Digite a string a compactar: ")
        if not s: print("String vazia."); return
        result = [];
        count = 1
        for i in range(1, len(s)):
            if s[i] == s[i - 1]:
                count += 1
            else:
                result.append(s[i - 1] + str(count));
                count = 1
        result.append(s[-1] + str(count))
        print("Compactado:", "".join(result))
    elif op == 'b':
        s = input("Digite a string RLE a descompactar: ")
        if not s: print("String vazia."); return
        try:
            result = ""
            for char, count_str in re.findall(r'(\D)(\d+)', s):
                result += char * int(count_str)
            print("Descompactado:", result)
        except Exception as e:
            print(f"Formato RLE inválido: {e}")
    else:
        print("Opção inválida.")


def stopwatch():
    input("Pressione ENTER para começar...")
    start_time = time.time();
    paused_time = 0.0;
    is_paused = False
    while True:
        elapsed = time.time() - start_time - paused_time
        print(f"\rTempo decorrido: {elapsed:.2f} s", end="")
        try:
            user_input = input().strip().lower()
            if user_input == 'p' and not is_paused:
                paused_start = time.time();
                is_paused = True
                print("\nCronômetro pausado. Pressione 'c' para continuar.")
            elif user_input == 'c' and is_paused:
                paused_time += time.time() - paused_start;
                is_paused = False
                print("Cronômetro continuando...")
            elif user_input == 's':
                print("\nCronômetro parado.");
                break
            elif not user_input:
                pass
        except KeyboardInterrupt:
            print("\nCronômetro parado via CTRL+C.");
            break


def simulacao_dados():
    num_dados = ler_int("Quantos dados (1-100): ")
    if num_dados is None or not (1 <= num_dados <= 100):
        print("Número inválido.");
        return
    num_lados = ler_int("Quantos lados por dado (>=2): ")
    if num_lados is None or num_lados < 2:
        print("Número inválido.");
        return

    resultados = [random.randint(1, num_lados) for _ in range(num_dados)]
    print("\nResultados individuais:", resultados)

    contagem = Counter(resultados)
    print("\nResumo:")
    for lado in range(1, num_lados + 1):
        freq = contagem.get(lado, 0)
        print(f"  Lado {lado}: {freq} ({freq / num_dados * 100:.2f}%)")


# --------------------
# Inteligência Artificial e Otimização
# --------------------

def gorjeta_fuzzy():
    print("Calculadora de gorjeta com Lógica Fuzzy")
    try:
        qualidade_servico = ler_float("Qualidade do serviço (0-10): ")
        qualidade_comida = ler_float("Qualidade da comida (0-10): ")
        if None in (qualidade_servico, qualidade_comida): return

        # Funções de pertinência (triangular/trapezoidal)
        def servico_ruim(x):
            """Função de pertinência para serviço ruim (rampa descendente)."""
            if 0 <= x <= 5:
                return max(0, (5 - x) / 5)
            return 0

        def servico_bom(x):
            """Função de pertinência para serviço bom (triangular)."""
            if 2.5 <= x <= 5:
                return (x - 2.5) / 2.5
            if 5 < x <= 7.5:
                return (7.5 - x) / 2.5
            return 0

        def servico_otimo(x):
            """Função de pertinência para serviço ótimo (rampa ascendente)."""
            if 5 <= x <= 10:
                return (x - 5) / 5
            return 0

        def comida_ruim(x):
            """Função de pertinência para comida ruim (rampa descendente)."""
            if 0 <= x <= 5:
                return (5 - x) / 5
            return 0

        def comida_boa(x):
            """Função de pertinência para comida boa (rampa ascendente)."""
            if 5 <= x <= 10:
                return (x - 5) / 5
            return 0

        # Fuzzyficação
        ruim_serv = servico_ruim(qualidade_servico)
        bom_serv = servico_bom(qualidade_servico)
        otimo_serv = servico_otimo(qualidade_servico)
        ruim_comida = comida_ruim(qualidade_comida)
        boa_comida = comida_boa(qualidade_comida)

        # Regras de inferência (AND = min, OR = max)
        gorjeta_baixa = max(ruim_serv, ruim_comida)
        gorjeta_media = bom_serv
        gorjeta_alta = otimo_serv * boa_comida

        # Defuzzificação (Centro de Gravidade) - Simplificado
        saidas = {
            "baixa": gorjeta_baixa,
            "media": gorjeta_media,
            "alta": gorjeta_alta
        }
        max_saida = max(saidas, key=saidas.get)
        print(f"\nGrau de pertinência para cada gorjeta:")
        for k, v in saidas.items(): print(f"  {k}: {v:.2f}")
        print(f"\nResultado da inferência: gorjeta de nível '{max_saida}'")
    except Exception as e:
        print("Erro durante a lógica fuzzy:", e)


def gradient_descent():
    print("Otimização por Gradiente Descendente para f(x)")
    print("Digite f(x) (ex: x**2 + 5*x + 6)")
    if not sympy_disponivel:
        print("SymPy não disponível. Esta função requer a biblioteca sympy.")
        return
    try:
        expr = input("f(x) = ")
        x = sp.symbols('x')
        f_sym = sp.sympify(expr)
        df_sym = sp.diff(f_sym, x)

        f = sp.lambdify(x, f_sym, 'math')
        df = sp.lambdify(x, df_sym, 'math')

        x_init = ler_float("Chute inicial para x: ")
        learning_rate = ler_float("Taxa de aprendizado (ex: 0.1): ") or 0.1
        epochs = ler_int("Número de iterações (ex: 100): ") or 100

        if None in (x_init, learning_rate, epochs): return

        x_current = x_init
        for i in range(epochs):
            x_current = x_current - learning_rate * df(x_current)

        print(f"Mínimo aproximado de f(x) encontrado em x = {x_current:.6g}")
        print(f"Valor da função neste ponto: f(x) = {f(x_current):.6g}")
    except Exception as e:
        print("Ocorreu um erro durante a otimização:", e)


# --------------------
# Fractais e gráficos ASCII
# --------------------

def mandelbrot_ascii(width: int = 80, height: int = 40, max_iter: int = 80, x_center: float = -0.5,
                     y_center: float = 0.0, scale: float = 1.5):
    """Desenha versão ASCII do conjunto de Mandelbrot."""
    chars = " .:-=+*#%@"
    for j in range(height):
        y = y_center + (j - height / 2) * (2 * scale / height)
        row = ""
        for i in range(width):
            x = x_center + (i - width / 2) * (2 * scale / width)
            zx, zy = 0.0, 0.0
            it = 0
            while zx * zx + zy * zy <= 4.0 and it < max_iter:
                zx, zy = zx * zx - zy * zy + x, 2 * zx * zy + y
                it += 1
            row += chars[int(it / max_iter * (len(chars) - 1))]
        print(row)


# --------------------
# Módulos de Menu
# --------------------

def menu_matematica_avancada():
    while True:
        print("\n--- MATEMÁTICA AVANÇADA ---")
        print("1. Análise Numérica (Bisseção, Newton, Simpson, Derivada)")
        print("2. Funções de Primos e Teoria dos Números")
        print("3. Raízes de Polinômios")
        print("0. Voltar")
        op = input("Escolha: ").strip()
        if op == '1':
            menu_analise_numerica()
        elif op == '2':
            menu_teoria_numeros()
        elif op == '3':
            polynomial_roots()
        elif op == '0':
            break
        else:
            print("Opção inválida.")


def menu_teoria_numeros():
    print("\n--- TEORIA DOS NÚMEROS ---")
    print(
        "a) Fatoração em Primos\nb) Função Totiente de Euler\nc) Exponenciação Modular\nd) MDC (Algoritmo de Euclides)\ne) MDC e Coeficientes de Bézout")
    op = input("Escolha: ").strip().lower()
    if op == 'a':
        n = ler_int("Número a fatorar: ")
        if n is not None: print("Fatoração:", fatoracao(n))
    elif op == 'b':
        n = ler_int("Número para phi(n): ")
        if n is not None:
            try:
                print(f"phi({n}) = {euler_totient(n)}")
            except ValueError as e:
                print(e)
    elif op == 'c':
        base = ler_int("Base: ");
        exp = ler_int("Expoente: ");
        mod = ler_int("Módulo: ")
        if None not in (base, exp, mod): print(f"({base}^{exp}) mod {mod} = {modular_exponentiation(base, exp, mod)}")
    elif op == 'd':
        a = ler_int("a: ");
        b = ler_int("b: ")
        if None not in (a, b): print(f"MDC({a}, {b}) = {gcd(a, b)}")
    elif op == 'e':
        a = ler_int("a: ");
        b = ler_int("b: ")
        if None not in (a, b):
            d, x, y = extended_gcd(a, b)
            print(f"MDC({a}, {b}) = {d}")
            print(f"Coeficientes de Bézout: {a}*{x} + {b}*{y} = {d}")
    else:
        print("Opção inválida.")


def menu_analise_numerica():
    print("\n-- Análise Numérica --")
    print("a) Bisseção\nb) Newton-Raphson\nc) Integral (Trapézio/Simpson)\nd) Derivada Numérica")
    op = input("Escolha: ").strip().lower()
    if op == 'a':
        print("Defina f(x) (requer sympy). Ex: x**3 - x - 2")
        if not sympy_disponivel: print("SymPy não disponível."); return
        expr = input("f(x) = ")
        x = sp.symbols('x');
        f_sym = sp.lambdify(x, sp.sympify(expr), 'math')
        a = ler_float("a: ");
        b = ler_float("b: ")
        try:
            root, it = metodo_bisseccao(f_sym, a, b); print(f"Raiz aprox: {root} (iter: {it})")
        except Exception as e:
            print("Erro:", e)
    elif op == 'b':
        print("Newton-Raphson (requer sympy)")
        if not sympy_disponivel: print("SymPy não disponível."); return
        expr = input("f(x) = ")
        x = sp.symbols('x');
        f_sym = sp.sympify(expr);
        df_sym = sp.diff(f_sym, x)
        f = sp.lambdify(x, f_sym, 'math');
        df = sp.lambdify(x, df_sym, 'math')
        x0 = ler_float("x0 inicial: ")
        try:
            root, it = metodo_newton(f, df, x0); print(f"Raiz: {root} (it: {it})")
        except Exception as e:
            print("Erro:", e)
    elif op == 'c':
        print("Integração numérica (requer sympy)")
        if not sympy_disponivel: print("SymPy não disponível."); return
        expr = input("f(x) = ")
        x = sp.symbols('x');
        f_sym = sp.lambdify(x, sp.sympify(expr), 'math')
        a = ler_float("a: ");
        b = ler_float("b: ")
        if None in (a, b): return
        print("1) Trapézio  2) Simpson");
        escolha = input("Escolha: ").strip()
        n = ler_int("Número de subdivisões (ex: 1000): ") or 1000
        if escolha == '1':
            print("Resultado (Trapézio):", integral_trapezio(f_sym, a, b, n))
        else:
            print("Resultado (Simpson):", integral_simpson(f_sym, a, b, n))
    elif op == 'd':
        print("Derivada numérica (requer sympy)")
        if not sympy_disponivel: print("SymPy não disponível."); return
        expr = input("f(x) = ")
        x = sp.symbols('x');
        f_sym = sp.lambdify(x, sp.sympify(expr), 'math')
        x_val = ler_float("x: ");
        h_val = ler_float("h (passo, ex: 1e-6): ") or 1e-6
        print("Derivada em", x_val, "é aprox:", derivada_numerica(f_sym, x_val, h_val))
    else:
        print("Opção inválida.")


def menu_algebra_linear():
    print("\n-- ÁLGEBRA LINEAR --")
    print(
        "1. Soma de matrizes\n2. Multiplicar matrizes\n3. Determinante\n4. Inversa\n5. Matriz Transposta\n6. Autovalores/Autovetores\n7. Resolver Sistema Linear (Ax=b)\n8. Decomposição LU\n9. Decomposição QR\n10. Matriz de Covariância\n11. Matriz de Vandermonde\n0. Voltar")
    op = input("Escolha: ").strip().lower()
    if op == '1':
        print("Matriz A:");
        A = matriz_from_input()
        print("Matriz B:");
        B = matriz_from_input()
        if A is None or B is None: return
        try:
            print("Resultado:\n", soma_matrizes(A, B))
        except Exception as e:
            print(f"Erro: {e}")
    elif op == '2':
        print("Matriz A:");
        A = matriz_from_input()
        print("Matriz B:");
        B = matriz_from_input()
        if A is None or B is None: return
        try:
            print("Resultado:\n", multiplicacao_matrizes(A, B))
        except Exception as e:
            print(f"Erro: {e}")
    elif op == '3':
        A = matriz_from_input()
        if A is None: return
        try:
            print("Determinante =", determinante(A))
        except Exception as e:
            print("Erro:", e)
    elif op == '4':
        A = matriz_from_input()
        if A is None: return
        try:
            print("Inversa:\n", inversa(A))
        except Exception as e:
            print("Erro:", e)
    elif op == '5':
        A = matriz_from_input()
        if A is None: return
        try:
            print("Transposta:\n", matriz_transposta(A))
        except Exception as e:
            print(f"Erro: {e}")
    elif op == '6':
        A = matriz_from_input()
        if A is None: return
        eigen_values_vectors(A)
    elif op == '7':
        A = matriz_from_input();
        b = vetor_from_input()
        if A is None or b is None: return
        solve_linear_system(A, b)
    elif op == '8':
        A = matriz_from_input()
        if A is None: return
        try:
            L, U = decomposicao_lu(A)
        except Exception as e:
            print(f"Erro: {e}"); return
        print("Matriz L:\n", L)
        print("\nMatriz U:\n", U)
    elif op == '9':
        A = matriz_from_input()
        if A is None: return
        try:
            Q, R = decomposicao_qr(A)
        except Exception as e:
            print(f"Erro: {e}"); return
        print("Matriz Q:\n", Q)
        print("\nMatriz R:\n", R)
    elif op == '10':
        print("Matriz de dados (amostras por linha):")
        dados = matriz_from_input()
        if dados is None: return
        try:
            cov = matriz_covariancia(dados)
            print("Matriz de Covariância:\n", cov)
        except Exception as e:
            print(f"Erro: {e}")
    elif op == '11':
        print("Vetor de entrada para a matriz de Vandermonde:")
        v = vetor_from_input()
        if v is None: return
        n = ler_int("Ordem da matriz (opcional, padrão = len(v)): ")
        try:
            vand = matriz_vandermonde(v, n)
            print("Matriz de Vandermonde:\n", vand)
        except Exception as e:
            print(f"Erro: {e}")
    elif op == '0':
        return
    else:
        print("Opção inválida.")


def menu_fisica():
    print("\n-- FÍSICA E ENGENHARIA --")
    print(
        "1) MRU\n2) MRUV\n3) Lançamento Oblíquo\n4) Lei de Ohm\n5) Energia Cinética\n6) Lei dos Gases Ideais\n7) Gravitação Universal\n8) Geometria de Sólidos\n9) Distância entre Pontos\n10) Operações Vetoriais\n11) Rotação de Vetores\n0) Voltar")
    op = input("Escolha: ").strip()
    if op == '1':
        mru()
    elif op == '2':
        mruv()
    elif op == '3':
        lancamento_obliquo()
    elif op == '4':
        lei_de_ohm()
    elif op == '5':
        energia_cinetica()
    elif op == '6':
        lei_dos_gases_ideais()
    elif op == '7':
        gravitacao_universal()
    elif op == '8':
        geometria_solidos()
    elif op == '9':
        distancia_pontos()
    elif op == '10':
        operacoes_vetoriais()
    elif op == '11':
        rotacao_vetores()
    elif op == '0':
        return
    else:
        print("Opção inválida.")


def menu_conversoes():
    print("\n-- CONVERSÕES CIENTÍFICAS E DE BASE --")
    print("1) Temperatura\n2) Velocidade\n3) Romanos <-> Árabes\n4) Base64 Encode/Decode\n0) Voltar")
    op = input("Escolha: ").strip()
    if op == '1':
        conversao_temperatura()
    elif op == '2':
        conversao_velocidade()
    elif op == '3':
        print("a) Romano -> Arábico\nb) Arábico -> Romano")
        sub_op = input("Escolha: ").strip().lower()
        if sub_op == 'a':
            romanos_para_arabicos()
        elif sub_op == 'b':
            arabicos_para_romanos()
        else:
            print("Opção inválida.")
    elif op == '4':
        base64_converter()
    elif op == '0':
        return
    else:
        print("Opção inválida.")


def menu_estatistica():
    print("\n-- ESTATÍSTICA E ANÁLISE DE DADOS --")
    print(
        "1) Estatística Básica (Média, Mediana, Desvio)\n2) Distribuição Normal (PDF/CDF)\n3) Binomial PMF\n4) Poisson PMF\n5) Regressão Linear Simples\n6) Coeficiente de Correlação\n0) Voltar")
    op = input("Escolha: ").strip()
    if op == '1':
        estatistica_basica()
    elif op == '2':
        x = ler_float("x: ");
        mu = ler_float("mu (padrão 0): ") or 0;
        sigma = ler_float("sigma (padrão 1): ") or 1
        print("PDF =", normal_pdf(x, mu, sigma));
        print("CDF =", normal_cdf(x, mu, sigma))
    elif op == '3':
        n = ler_int("n: ");
        p = ler_float("p (0-1): ");
        k = ler_int("k: ")
        if None in (n, p, k): return
        print("PMF binomial =", distribuicao_binomial_pmf(k, n, p))
    elif op == '4':
        lam = ler_float("lambda: ");
        k = ler_int("k: ")
        if None in (lam, k): return
        print("PMF Poisson =", distribuicao_poisson_pmf(k, lam))
    elif op == '5':
        regressao_linear_simples()
    elif op == '6':
        coeficiente_correlacao()
    else:
        print("Opção inválida.")


def menu_utilitarios():
    print("\n-- UTILITÁRIOS --")
    print(
        "1) Texto -> ASCII\n2) Conversor de base\n3) Hash (MD5/SHA1/SHA256)\n4) Cifra de César\n5) Cifra de Vigenère\n6) Cronômetro\n7) Compressão de Texto (RLE)\n8) Estruturas de Dados (Pilha, Fila)\n9) Simulação de Dados")
    op = input("Escolha: ").strip()
    if op == '1':
        texto_para_ascii()
    elif op == '2':
        conversao_base()
    elif op == '3':
        gerar_hash()
    elif op == '4':
        cifra_cesar()
    elif op == '5':
        cifra_vigenere()
    elif op == '6':
        stopwatch()
    elif op == '7':
        rle_converter()
    elif op == '8':
        menu_estruturas_dados()
    elif op == '9':
        simulacao_dados()
    else:
        print("Opção inválida.")


def menu_ia_otimizacao():
    print("\n--- IA E OTIMIZAÇÃO ---")
    print("1) Gorjeta com Lógica Fuzzy\n2) Otimização (Gradiente Descendente)\n0) Voltar")
    op = input("Escolha: ").strip()
    if op == '1':
        gorjeta_fuzzy()
    elif op == '2':
        gradient_descent()
    elif op == '0':
        return
    else:
        print("Opção inválida.")


def menu_extremo():
    while True:
        print("\n=== MÓDULO AVANÇADO ===")
        print("1. Matemática Avançada (Números, Polinômios)")
        print("2. Álgebra Linear (Matrizes)")
        print("3. Física e Engenharia")
        print("4. Conversões Científicas e de Base")
        print("5. Estatística e Análise de Dados")
        print("6. Utilitários (Hash, Cripto, Cronômetro...)")
        print("7. IA e Otimização")
        print("8. Fractais: Mandelbrot ASCII")
        print("9. Constantes científicas")
        print("0. Voltar")
        op = input("Escolha: ").strip()
        if op == '1':
            menu_matematica_avancada()
        elif op == '2':
            menu_algebra_linear()
        elif op == '3':
            menu_fisica()
        elif op == '4':
            menu_conversoes()
        elif op == '5':
            menu_estatistica()
        elif op == '6':
            menu_utilitarios()
        elif op == '7':
            menu_ia_otimizacao()
        elif op == '8':
            try:
                mandelbrot_ascii(width=80, height=32, max_iter=120)
            except Exception as e:
                print("Erro ao gerar Mandelbrot:", e)
        elif op == '9':
            for k, v in CONSTANTES.items(): print(f"{k} = {v}")
        elif op == '0':
            break
        else:
            print("Opção inválida.")


# Funções originais
def operacoes_basicas():
    print("\n-- Operações Básicas --")
    print("a) +  b) -  c) * d) /  e) ^  f) sqrt  g) n-root")
    op = input("Escolha: ").strip().lower()
    try:
        if op in ['a', 'b', 'c', 'd', 'e']:
            x = float(input("x: "));
            y = float(input("y: "))
            if op == 'a': print(x + y)
            if op == 'b': print(x - y)
            if op == 'c': print(x * y)
            if op == 'd': print(x / y) if y != 0 else print("Erro: divisão por zero")
            if op == 'e': print(x ** y)
        elif op == 'f':
            x = float(input("x: "));
            print(cmath.sqrt(x) if x < 0 else math.sqrt(x))
        elif op == 'g':
            x = float(input("x: "));
            n = float(input("n: "))
            if n == 0: print("Índice inválido"); return
            is_int_n = abs(n - round(n)) < 1e-12
            if x < 0 and is_int_n and int(round(n)) % 2 == 0:
                print("Raiz par de negativo: complexo", complex(x) ** (1.0 / n))
            else:
                print((complex(x) if x < 0 else x) ** (1.0 / n))
        else:
            print("Opção inválida")
    except Exception as e:
        print("Erro:", e)


def funcoes_trigonometricas():
    print("\n-- Trigonometria --")
    modo = input("Graus (g) ou rad (r)? ").strip().lower()
    op = input("a) sin b) cos c) tan d) asin e) acos f) atan g) atan2\nEscolha: ").strip().lower()
    try:
        if op in ['a', 'b', 'c']:
            x = float(input("Ângulo: "));
            x = math.radians(x) if modo == 'g' else x
            if op == 'a': print(math.sin(x))
            if op == 'b': print(math.cos(x))
            if op == 'c':
                cosx = math.cos(x)
                if abs(cosx) < 1e-12: print("Aviso: ponto próximo de assíntota")
                print(math.tan(x))
        elif op in ['d', 'e', 'f']:
            x = float(input("Valor (razão): "))
            if op in ['d', 'e'] and abs(x) > 1: print("Fora do domínio"); return
            r = math.asin(x) if op == 'd' else math.acos(x) if op == 'e' else math.atan(x)
            r = math.degrees(r) if modo == 'g' else r
            print(r)
        elif op == 'g':
            y = float(input("y: "));
            x = float(input("x: "))
            r = math.atan2(y, x);
            r = math.degrees(r) if modo == 'g' else r
            print(r)
    except Exception as e:
        print("Erro:", e)


def funcoes_hiperbolicas():
    print("\n-- Hiperbólicas --")
    op = input("a)sinh b)cosh c)tanh d)asinh e)acosh f)atanh\nEscolha: ").strip().lower()
    try:
        x = float(input("x: "))
        if op == 'a':
            print(math.sinh(x))
        elif op == 'b':
            print(math.cosh(x))
        elif op == 'c':
            print(math.tanh(x))
        elif op == 'd':
            print(math.asinh(x))
        elif op == 'e':
            if x < 1: print("Fora do domínio"); return
            print(math.acosh(x))
        elif op == 'f':
            if x <= -1 or x >= 1: print("Fora do domínio"); return
            print(math.atanh(x))
    except Exception as e:
        print("Erro:", e)


def logaritmos_e_exponenciais():
    print("\n-- Log/Exp --")
    op = input("a)log10 b)ln c)exp d)log base e)dec->científica f)científica->dec\nEscolha: ").strip().lower()
    try:
        if op == 'a':
            x = float(input("x (>0): "));
            print(math.log10(x))
        elif op == 'b':
            x = float(input("x (>0): "));
            print(math.log(x))
        elif op == 'c':
            x = float(input("expoente: "));
            print(math.exp(x))
        elif op == 'd':
            x = float(input("x>0: "));
            base = float(input("base>0 !=1: "));
            print(math.log(x, base))
        elif op == 'e':
            s = input("decimal: ");
            print(format(float(s), '.6e'))
        elif op == 'f':
            s = input("notação científica (ex: 1.23e4): ");
            print(float(s))
    except Exception as e:
        print("Erro:", e)


def fatorial_permutacao_combinacao():
    print("\n-- Fatorial/Perm/Comb/Gamma --")
    op = input("a)! b)P(n,r) c)C(n,r) d)Gamma\nEscolha: ").strip().lower()
    try:
        if op == 'a':
            n = int(input("n (>=0): "));
            print(math.factorial(n))
        elif op in ['b', 'c']:
            n = int(input("n: "));
            r = int(input("r: "))
            if r > n: print("r>n"); return
            if op == 'b':
                print(math.factorial(n) // math.factorial(n - r))
            else:
                print(math.comb(n, r))
        elif op == 'd':
            x = float(input("x: "));
            print(math.gamma(x))
    except Exception as e:
        print("Erro:", e)


def conversoes_basicas():
    print("\n-- Conversões Numéricas --")
    print("a)deg->rad b)rad->deg c)dec->bin d)bin->dec e)dec->oct f)oct->dec g)dec->hex h)hex->dec")
    op = input("Escolha: ").strip().lower()
    try:
        if op == 'a':
            g = float(input("graus: "));
            print(math.radians(g))
        elif op == 'b':
            r = float(input("radianos: "));
            print(math.degrees(r))
        elif op == 'c':
            dec = int(input("decimal: "));
            print(bin(dec)[2:])
        elif op == 'd':
            b = input("binário: ");
            print(int(b, 2))
        elif op == 'e':
            dec = int(input("decimal: "));
            print(oct(dec)[2:])
        elif op == 'f':
            o = input("octal: ");
            print(int(o, 8))
        elif op == 'g':
            dec = int(input("decimal: "));
            print(hex(dec)[2:])
        elif op == 'h':
            h = input("hex: ");
            print(int(h, 16))
    except Exception as e:
        print("Erro:", e)


def estatistica_basica():
    print("\n-- Estatística Básica --")
    print("Digite números separados por espaço:")
    try:
        dados = list(map(float, input().split()))
        if not dados: print("Lista vazia"); return
        print("Média:", statistics.mean(dados))
        print("Mediana:", statistics.median(dados))
        if len(dados) > 1:
            print("Variância:", statistics.variance(dados))
            print("Desvio:", statistics.stdev(dados))
    except Exception as e:
        print("Erro:", e)


def numeros_complexos():
    print("\n-- Números Complexos --")
    try:
        z1 = complex(input("z1 (ex: 3+4j): ").strip());
        z2 = complex(input("z2: ").strip())
        print("Soma:", z1 + z2);
        print("Subtração:", z1 - z2);
        print("Multiplicação:", z1 * z2)
        try:
            print("Divisão:", z1 / z2)
        except ZeroDivisionError:
            print("Divisão por zero!")
        print("Módulo:", abs(z1));
        print("Argumento (rad):", cmath.phase(z1))
        print("Conjugado:", z1.conjugate())
    except Exception as e:
        print("Erro:", e)


def funcoes_adicionais():
    print("\n-- Funções Adicionais --")
    print("a)Primo? b)Próximos n primos c)MMC d)MDC e)Bit ops f)Fatores primos")
    op = input("Escolha: ").strip().lower()

    def is_prime(num):
        if num <= 1: return False
        if num <= 3: return True
        if num % 2 == 0 or num % 3 == 0: return False
        i = 5
        while i * i <= num:
            if num % i == 0 or num % (i + 2) == 0: return False
            i += 6
        return True

    if op == 'a':
        n = ler_int("n: ");
        print(is_prime(n))
    elif op == 'b':
        n = ler_int("Quantos primos: ");
        count = 0;
        num = 2;
        primos = []
        while count < n:
            if is_prime(num): primos.append(num); count += 1
            num += 1
        print(primos)
    elif op == 'c':
        a = ler_int("a: ");
        b = ler_int("b: ")
        if None not in (a, b): print("MMC:", abs(a * b) // gcd(a, b) if a != 0 and b != 0 else 0)
    elif op == 'd':
        a = ler_int("a: ");
        b = ler_int("b: ")
        if None not in (a, b): print("MDC:", gcd(a, b))
    elif op == 'e':
        x = ler_int("x: ");
        y = ler_int("y: ")
        if None not in (x, y): print("AND:", x & y, "OR:", x | y, "XOR:", x ^ y)
    elif op == 'f':
        n = ler_int("n: ")
        if n is not None: print("Fatoração:", fatoracao(n))
    else:
        print("Opção inválida.")


def ascii_plot(xs, ys, title="Gráfico", xlabel="x", ylabel="y", width=None, height=20):
    pts = [(x, y) for x, y in zip(xs, ys) if
           y is not None and not (isinstance(y, float) and (math.isnan(y) or math.isinf(y)))]
    if not pts: print("Nenhum ponto válido."); return
    xs_valid = [p[0] for p in pts];
    ys_valid = [p[1] for p in pts]
    xmin, xmax = min(xs_valid), max(xs_valid);
    ymin, ymax = min(ys_valid), max(ys_valid)
    if abs(xmax - xmin) < 1e-12: xmin -= 1; xmax += 1
    if abs(ymax - ymin) < 1e-12: ymin -= 1; ymax += 1
    try:
        cols = shutil.get_terminal_size().columns
    except Exception:
        cols = 80
    if width is None: width = min(80, max(40, cols - 10))
    height = max(10, int(height));
    grid = [[" " for _ in range(width)] for _ in range(height)]

    def map_point(x, y):
        col = int((x - xmin) / (xmax - xmin) * (width - 1))
        row = int((ymax - y) / (ymax - ymin) * (height - 1))
        return max(0, min(height - 1, row)), max(0, min(width - 1, col))

    for x, y in pts:
        if isinstance(y, float) and (math.isinf(y) or math.isnan(y) or abs(y) > 1e6): continue
        r, c = map_point(x, y);
        grid[r][c] = "*"
    if xmin <= 0 <= xmax:
        x0_col = int((0 - xmin) / (xmax - xmin) * (width - 1))
        for r in range(height):
            if grid[r][x0_col] == " ": grid[r][x0_col] = "|"
    if ymin <= 0 <= ymax:
        y0_row = int((ymax - 0) / (ymax - ymin) * (height - 1))
        for c in range(width):
            if grid[y0_row][c] == " ": grid[y0_row][c] = "-"
    print(f"\n{title}")
    for row in grid: print("".join(row))
    print(f"{xlabel}: [{xmin:.4g}, {xmax:.4g}]    {ylabel}: [{ymin:.4g}, {ymax:.4g}]")
    print("('*' pontos, '|' eixo y, '-' eixo x)")


def graficos():
    print("\n-- Gráficos --")
    print("a) sin b) cos c) tan d) exp e) ln f) polinomial")
    opc = input("Escolha: ").strip().lower()
    try:
        x_start = float(input("x start: "));
        x_end = float(input("x end: "))
        passos = int(input("pontos (ex: 200): "))
        if passos <= 1 or x_end <= x_start: print("Intervalo inválido."); return
        xs = [x_start + i * (x_end - x_start) / (passos - 1) for i in range(passos)]
        ys = [];
        titulo = ""
        if opc == 'a':
            ys = [math.sin(x) for x in xs]; titulo = "sin(x)"
        elif opc == 'b':
            ys = [math.cos(x) for x in xs]; titulo = "cos(x)"
        elif opc == 'c':
            ys_tmp = []
            for val in xs:
                try:
                    y = math.tan(val)
                except ValueError:
                    y = None
                ys_tmp.append(y if abs(y) < 1e6 else None)
            ys = ys_tmp;
            titulo = "tan(x)"
        elif opc == 'd':
            ys = [];
            for x in xs:
                try:
                    y = math.exp(x)
                except OverflowError:
                    y = None
                ys.append(y if y is not None and abs(y) < 1e12 else None)
            titulo = "exp(x)"
        elif opc == 'e':
            if any(x <= 0 for x in xs): print("ln(x): intervalo deve ser > 0"); return
            ys = [math.log(x) for x in xs];
            titulo = "ln(x)"
        elif opc == 'f':
            a = float(input("a: "));
            b = float(input("b: "));
            c = float(input("c: "))
            ys = [a * x ** 2 + b * x + c for x in xs];
            titulo = f"{a}x^2+{b}x+{c}"
        else:
            print("Inválido"); return
        if plotext_disponivel:
            try:
                plt.clear_figure();
                plt.title(titulo)
                seg_x, seg_y = [], []
                for x, y in zip(xs, ys):
                    if y is None or math.isnan(y) or math.isinf(y):
                        if seg_x: plt.plot(seg_x, seg_y); seg_x, seg_y = [], []
                    else:
                        seg_x.append(x); seg_y.append(y)
                if seg_x: plt.plot(seg_x, seg_y)
                plt.show()
                return
            except Exception:
                print("plotext falhou; fallback ASCII.")
        ys_for_ascii = [y if y is not None else float('nan') for y in ys]
        ys_mapped = [None if (isinstance(y, float) and (math.isnan(y) or math.isinf(y))) else y for y in ys_for_ascii]
        ascii_plot(xs, ys_mapped, title=titulo)
    except Exception as e:
        print("Erro:", e)


# --------------------
# Programa principal
# --------------------

def menu_principal():
    print("\n=== CALCULADORA CIENTÍFICA EXTREMA (EXPANDED) ===")
    print("1. Operações Básicas")
    print("2. Funções Trigonométricas")
    print("3. Funções Hiperbólicas")
    print("4. Logaritmos, Exponenciais e Potências")
    print("5. Fatorial, Permutação, Combinação e Gamma")
    print("6. Conversões Numéricas")
    print("7. Estatística Básica")
    print("8. Números Complexos")
    print("9. Funções Adicionais")
    print("10. Gráficos no Console (ASCII ou plotext)")
    print("11. Módulo Avançado (métodos numéricos, álgebra linear, física...)")
    print("0. Sair")
    return input("Escolha uma opção: ").strip()


def main():
    while True:
        escolha = menu_principal()
        if escolha == '1':
            operacoes_basicas()
        elif escolha == '2':
            funcoes_trigonometricas()
        elif escolha == '3':
            funcoes_hiperbolicas()
        elif escolha == '4':
            logaritmos_e_exponenciais()
        elif escolha == '5':
            fatorial_permutacao_combinacao()
        elif escolha == '6':
            conversoes_basicas()
        elif escolha == '7':
            estatistica_basica()
        elif escolha == '8':
            numeros_complexos()
        elif escolha == '9':
            funcoes_adicionais()
        elif escolha == '10':
            graficos()
        elif escolha == '11':
            menu_extremo()
        elif escolha == '0':
            print("Encerrando. Até logo!"); sys.exit(0)
        else:
            print("Opção inválida. Tente novamente.")


if __name__ == "__main__":
    main()