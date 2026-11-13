"""Exact rational check of the two-state instance of STATEMENTS SYS-6 (evidence for the Lean target).

S = {0,1}, A = {a0,a1,a2}, one human, one goal.  State 0: every action returns to 0, reward 1/20.
State 1: a0, a1 -> state 0 (reward 1/20); a2 -> state 1 (reward 1).  Linear V_h, gamma_h = 2/3,
gamma_r = 4/5, zeta = 2, xi = 1, eta = 3 (so U = -Ve^(-6)), beta = 2.
With p = pi(1)(a2):  solutions of the system <-> zeros of g in (0,1).
"""
from fractions import Fraction as F

u0, u1, gh, gr, e, beta = F(1, 20), F(1), F(2, 3), F(4, 5), 6, 2

def g(p):
    Ve0 = u0 / (1 - gh)                       # Ve(0) = u0 + gh Ve(0)
    V0 = -Ve0 ** (-e) / (1 - gr)              # Vr(0) = U(0) + gr Vr(0)
    Ve1 = ((1 - p) * Ve0 + p * u1) / (1 - gh * p)
    V1 = (-Ve1 ** (-e) + (1 - p) * gr * V0) / (1 - gr * p)
    r = (V1 / V0) ** (-beta)                  # (-Q(1,a2))^-beta / (-Q(1,a0))^-beta
    return p - r / (2 + r)

pts = [F(1, 2), F(3, 5), F(19, 20), F(99, 100), 1 - F(1, 10**12), 1 - F(1, 10**20)]
signs = [g(p) > 0 for p in pts]
print([(str(p), s) for p, s in zip(pts, signs)])
assert signs == [False, True, True, False, False, True]   # three sign changes => >= 3 solutions
