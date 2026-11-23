#!/usr/bin/env python3
"""Independent reconstruction of the star and triangle pairing checks,
including the four-site square and calibration with the star pairs.
"""
import numpy as np, itertools
I2 = np.eye(2); X = np.array([[0, 1], [1, 0]], complex); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1.0, -1.0]).astype(complex)
def swap(a, b):
    M = np.zeros((16, 16))
    for x in range(16):
        bits = [(x >> (3 - k)) & 1 for k in range(4)]; bits[a], bits[b] = bits[b], bits[a]
        M[int("".join(map(str, bits)), 2), x] = 1
    return M
S = {frozenset(e): swap(*e) for e in itertools.combinations(range(4), 2)}
PART = [(frozenset({0, 1}), frozenset({2, 3})), (frozenset({0, 2}), frozenset({1, 3})), (frozenset({0, 3}), frozenset({1, 2}))]
allsw = sum(S.values()); w, V = np.linalg.eigh(allsw)
Pj = {j: V[:, np.isclose(w, val)] @ V[:, np.isclose(w, val)].conj().T for j, val in ((0, 0), (1, 2), (2, 6))}
# code space and logical frame: the three 'yes' states are the +1 states of -S on either pair of the partition
code = V[:, np.isclose(w, 0)]                                                  # 16 x 2
Llog = [code.conj().T @ (-S[p[0]]) @ code for p in PART]                       # logical signed observables L_a (2x2)
assert all(np.allclose(code.conj().T @ (-S[p[0]]) @ code, code.conj().T @ (-S[p[1]]) @ code) for p in PART)
bl = lambda A: np.real(np.array([np.trace(A @ P) for P in (X, Y, Z)])) / 2
n = np.array([bl(L) for L in Llog])
print("A. LOGICAL STRUCTURE: each L_a squares to one:", all(np.allclose(L @ L, I2) for L in Llog), "; they sum to zero:", np.allclose(sum(Llog), 0),
      "; pairwise angles (cos):", np.round([n[0] @ n[1], n[0] @ n[2], n[1] @ n[2]], 3))

print("\nB. THE EIGHT FIXED WIRINGS (one pair chosen from each of the three partitions)")
e1 = n[0]; e2 = n[1] - (n[1] @ e1) * e1; e2 /= np.linalg.norm(e2)
def ceiling(edges, grid=3600):
    best = 0.0
    for ang in np.linspace(0, 2 * np.pi, grid, endpoint=False):
        m = np.cos(ang) * e1 + np.sin(ang) * e2
        O = 0.5 * np.eye(16) + sum((m @ n[a]) * (np.eye(16) - S[edges[a]]) / 2 for a in range(3)) / 3
        best = max(best, np.linalg.eigvalsh(O).max())
    return best
for choice in itertools.product((0, 1), repeat=3):
    edges = [PART[a][choice[a]] for a in range(3)]
    common = frozenset.intersection(*edges)
    verts = frozenset.union(*edges)
    kind = "star" if len(common) == 1 else ("triangle" if len(verts) == 3 else "?")
    print(f"   pairs {[''.join(str(i + 1) for i in sorted(e)) for e in edges]}: {kind:8s} sharp ceiling for a boundary without quantum memory {ceiling(edges):.8f}")
print(f"   reference values: 1/2 + (1 + sqrt 33)/24 = {0.5 + (1 + np.sqrt(33)) / 24:.8f} and 3/4")

print("\nC. THE TRIANGLE REDUCTION (sites 1,2,3 measured, site 4 ignored)")
tri = S[frozenset({0, 1})] + S[frozenset({0, 2})] + S[frozenset({1, 2})]
wt, Vt = np.linalg.eigh(tri)
print("   sum of the three swaps takes the values", sorted({abs(float(v)) for v in np.round(wt, 6)}), "with dimensions", [int(np.isclose(wt, v).sum()) for v in sorted(set(np.round(wt, 6)))])
low = Vt[:, np.isclose(wt, 0)]
R = [low.conj().T @ (-S[e]) @ low for e in (frozenset({0, 1}), frozenset({0, 2}), frozenset({1, 2}))]
print("   on the 8-dimensional sector where the sum is zero: each -swap squares to one:", all(np.allclose(r @ r, np.eye(8)) for r in R),
      "; any two anticommute to -1:", all(np.allclose(R[i] @ R[j] + R[j] @ R[i], -np.eye(8)) for i, j in ((0, 1), (0, 2), (1, 2))),
      "; on the other sector every swap is +1:", np.allclose(Vt[:, np.isclose(wt, 3)].conj().T @ S[frozenset({0, 1})] @ Vt[:, np.isclose(wt, 3)], np.eye(8)))

print("\nD. THE DECODER AND ITS IDENTITY   D*(L_a) = B_a + C,  C = P_1/3 + P_2")
A = [(S[p[0]] + S[p[1]]) / 2 for p in PART]; B = [-a for a in A]
A1 = [Pj[1] @ a @ Pj[1] for a in A]
print("   in the middle sector the three A_a are projectors:", all(np.allclose(a @ a, a) for a in A1), "; mutually orthogonal:", all(np.allclose(A1[i] @ A1[j], 0) for i, j in ((0, 1), (0, 2), (1, 2))),
      "; summing to that sector:", np.allclose(sum(A1), Pj[1]), "; ranks", [int(round(np.trace(a).real)) for a in A1])
def D_adjoint(Xlog):                                                             # Heisenberg picture of the decoder
    out = code @ Xlog @ code.conj().T
    for a in range(3): out = out + A1[a] * np.trace(Xlog @ (I2 / 2 - Llog[a] / 3))
    return out + Pj[2] * np.trace(Xlog) / 2
C = Pj[1] / 3 + Pj[2]
print("   prepared states I/2 - L_a/3 are valid (smallest eigenvalue):", round(float(min(np.linalg.eigvalsh(I2 / 2 - L / 3).min() for L in Llog)), 4),
      "; decoder is unital in the Heisenberg picture (trace preserving):", np.allclose(D_adjoint(I2), np.eye(16)))
print("   identity holds for a = 1, 2, 3:", [bool(np.allclose(D_adjoint(Llog[a]), B[a] + C)) for a in range(3)])
print("   sum of the physical observables equals -P_1 - 3 P_2 (so no decoder can preserve every raw probability):", np.allclose(sum(B), -Pj[1] - 3 * Pj[2]))

print("\nE. POOLED SCORE IS PRESERVED FOR ANY OPERATION; SEPARATE NORMALISATION BREAKS IT")
rng = np.random.default_rng(77)
def rand_cp(nk=3, scale=1.0):                                                    # Kraus operators 16 x 2, trace non-increasing
    Ks = [(rng.standard_normal((16, 2)) + 1j * rng.standard_normal((16, 2))) for _ in range(nk)]
    G = sum(k.conj().T @ k for k in Ks); c = scale / np.linalg.eigvalsh(G).max()
    return [k * np.sqrt(c) for k in Ks]
inputs = [((I2 + s * Llog[a]) / 2, a, s) for a in range(3) for s in (1, -1)]
worst = 0.0
for _ in range(300):
    Ks = rand_cp(rng.integers(1, 5), rng.uniform(0.3, 1.0))
    num_p = num_d = acc = 0.0
    for rho, a, s in inputs:
        out = sum(k @ rho @ k.conj().T for k in Ks); t = np.trace(out).real
        num_p += (t + s * np.trace(out @ B[a]).real) / 2; num_d += (t + s * np.trace(out @ D_adjoint(Llog[a])).real) / 2; acc += t
    worst = max(worst, abs(num_p / acc - num_d / acc))
print(f"   300 random operations (coherent, with and without discarding): largest difference between physical and decoded pooled score {worst:.2e}")
# the stated counterexample: measure L_1; '+' accepted, output a spin-2 state; '-' accepted with 1/3, output the mixed code state
spin2 = np.zeros(16); spin2[0] = 1.0; S2 = np.outer(spin2, spin2); mixcode = code @ code.conj().T / 2
rates_p, rates_d = [], []
for rho, a, s in inputs:
    pp = np.trace(rho @ (I2 + Llog[0]) / 2).real; pm = 1 - pp
    out = pp * S2 + pm / 3 * mixcode; t = np.trace(out).real
    rates_p.append((t + s * np.trace(out @ B[a]).real) / 2 / t); rates_d.append((t + s * np.trace(out @ D_adjoint(Llog[a])).real) / 2 / t)
from fractions import Fraction as Fr
print(f"   stated filter, mean of the six separately normalised rates: physical {np.mean(rates_p):.6f} (29/60 = {29/60:.6f}), decoded {np.mean(rates_d):.6f}")

print("\nF. UNIFORM CHOICE AMONG THE FOUR TRIANGLES AGAINST THE FAIR COMPLEMENTARY-PAIR RECEIVER")
tris = [c for c in itertools.combinations(range(4), 3)]
for a, p in enumerate(PART):
    used = [next(e for e in p if e <= frozenset(t)) for t in tris]
    print(f"   partition {a + 1}: pair used by each triangle {[''.join(str(i + 1) for i in sorted(e)) for e in used]} -> each of its two pairs twice: {sorted([used.count(p[0]), used.count(p[1])]) == [2, 2]}")

print("\nG. THE SIX LABELS ROUND THE HEXAGON")
ang = lambda v: np.degrees(np.arctan2(v @ e2, v @ e1)) % 360
order = sorted([(ang(s * n[a]), a + 1, s) for a in range(3) for s in (1, -1)])
print("   by angle:", [(round(t), f"axis {a}", "+" if s > 0 else "-") for t, a, s in order])
print("   signs alternate round the hexagon:", all(order[i][2] == -order[(i + 1) % 6][2] for i in range(6)), "; steps of 60 degrees:", np.allclose(np.diff([o[0] for o in order]), 60))
print("   so sum_k (-1)^k rho_k = 0 and a shift k -> k+d is the rotation by 60 d degrees: the cancellation of the note holds for every d")

# ---------------------------------------------------------------------------------------------------------------
# Additional checks of routing, calibration, and the same-trial witness.
print("\nH. THE STAR VALUE IN CLOSED FORM")
# In the middle sector the three star swaps are reflections; the game operator there is 1/2 + lam/6 with lam a root of
#   lam^3 - (9/4) lam - cos(3 theta) = 0,   theta the angle of the measured direction from the first signal axis.
def top_root(c3): return max(np.roots([1.0, 0.0, -9.0 / 4.0, -c3]).real)
star = [PART[a][0] if 0 in PART[a][0] else PART[a][1] for a in range(3)]                    # pairs 12, 13, 14
worst = 0.0
for theta in np.linspace(0, 2 * np.pi, 97):
    m = np.cos(theta) * e1 + np.sin(theta) * e2
    O = 0.5 * np.eye(16) + sum((m @ n[a]) * (np.eye(16) - S[star[a]]) / 2 for a in range(3)) / 3
    lam_mid = np.linalg.eigvalsh(Pj[1] @ O @ Pj[1]).max()
    worst = max(worst, abs(lam_mid - (0.5 + top_root(np.cos(3 * theta)) / 6)))
print(f"   largest difference between the middle-sector eigenvalue and 1/2 + (top root of the cubic)/6 over 97 angles: {worst:.2e}")
print(f"   at cos 3 theta = 1 the cubic factors as (lam + 1/2)(lam^2 - lam/2 - 2): top root {top_root(1.0):.8f} = (1 + sqrt 33)/4 = {(1 + np.sqrt(33)) / 4:.8f};"
      f" at cos 3 theta = -1: {0.5 + top_root(-1.0) / 6:.6f} (below 3/4)")

print("\nI. A REWRITTEN SHARE ONLY RELABELS THE MEASURED DIRECTION (any fixed wiring, no decoder needed)")
hexv = [np.cos(k * np.pi / 3) * e1 + np.sin(k * np.pi / 3) * e2 for k in range(6)]         # label k: hexagon direction
def signed_B(edges, v):                                                                     # +B_a or -B_a for v = +n_a or -n_a
    for a in range(3):
        if np.allclose(v, n[a]): return -S[edges[a]]
        if np.allclose(v, -n[a]): return S[edges[a]]
    raise ValueError
tri = [PART[0][0], PART[1][0], next(e for e in PART[2] if e <= frozenset({0, 1, 2}))]      # pairs 12, 13, 23
for name, edges in (("star", star), ("triangle", tri)):
    out = []
    for d in range(6):
        best = 0.0; gap = 0.0
        for theta in np.linspace(0, 2 * np.pi, 720, endpoint=False):
            m = np.cos(theta) * e1 + np.sin(theta) * e2
            G = sum((1 + m @ hexv[k]) / 2 * (np.eye(16) + signed_B(edges, hexv[(k + d) % 6])) / 2 for k in range(6)) / 6 * 2     # shifted game operator, unit weight
            best = max(best, np.linalg.eigvalsh(G).max())
            mr = np.cos(theta + d * np.pi / 3) * e1 + np.sin(theta + d * np.pi / 3) * e2
            O = 0.5 * np.eye(16) + sum((mr @ n[a]) * (np.eye(16) - S[edges[a]]) / 2 for a in range(3)) / 3
            gap = max(gap, np.abs(G - O).max())
        out.append((float(round(best, 6)), f"{gap:.0e}"))
    print(f"   {name:8s}: for shifts d = 0..5 (largest eigenvalue over directions, distance to the unshifted operator at the turned direction): {out}")

print("\nJ. THE FIXED-TRIANGLE DECODER:  keep the two-level label of sites 1,2,3 where their spin is 1/2, prepare I/2 where it is 3/2")
P32 = Vt[:, np.isclose(wt, 3)] @ Vt[:, np.isclose(wt, 3)].conj().T; P12 = np.eye(16) - P32
Btri = [-S[e] for e in tri]
ok = []
for a in range(3):
    lhs = P12 @ Btri[a] @ P12            # on the spin-1/2 sector the decoded logical observable is the physical one; elsewhere tr(L_a)/2 = 0
    ok.append(bool(np.allclose(lhs, Btri[a] + P32)))
print("   D*(L_a) = B_a + C with C the projector on the three-site spin-3/2 sector, a = 1, 2, 3:", ok)
print("   and the logical observables there are the same trine as the code's:", all(np.allclose(code.conj().T @ Btri[a] @ code, Llog[a]) for a in range(3)))

print("\nK. WHICH SIGNAL STATES A FOUR-SITE RING WITH EQUAL NEIGHBOUR EXCHANGE ALREADY CONTAINS (sites numbered round the square: 1-2-3-4-1)")
ring = [frozenset({0, 1}), frozenset({1, 2}), frozenset({2, 3}), frozenset({3, 0})]
Hring = sum(S[e] for e in ring) / 2                         # Heisenberg ring up to a constant: S_i.S_j = (swap)/2 - 1/4
wr, Vr = np.linalg.eigh(Hring); ground = Vr[:, 0]
print("   ground level of the equal-exchange ring is non-degenerate:", bool(wr[1] - wr[0] > 1e-9), "; total spin zero:", bool(np.isclose(ground @ Pj[0] @ ground, 1)))
sing = lambda e: (np.eye(16) - S[e]) / 2
def pair_state(p):                                           # the code state with a singlet on each pair of partition p
    v = code @ np.linalg.eigh(code.conj().T @ (sing(p[0]) @ sing(p[1])) @ code)[1][:, -1]; return v / np.linalg.norm(v)
x_part = (frozenset({0, 1}), frozenset({2, 3})); y_part = (frozenset({1, 2}), frozenset({0, 3})); d_part = (frozenset({0, 2}), frozenset({1, 3}))
vx, vy, vd = pair_state(x_part), pair_state(y_part), pair_state(d_part)
print(f"   overlaps squared between the three singlet-pair states: {abs(vx @ vy) ** 2:.4f}, {abs(vx @ vd) ** 2:.4f}, {abs(vy @ vd) ** 2:.4f}")
print(f"   ring ground state against the diagonal singlet-pair state: overlap squared {abs(ground @ vd) ** 2:.4f}  (0 means it is the MINUS state of the diagonal setting)")
print(f"   in the ring ground state: P(12 and 34 both singlets) = {ground @ sing(x_part[0]) @ sing(x_part[1]) @ ground:.4f}, P(23 and 14 both singlets) = {ground @ sing(y_part[0]) @ sing(y_part[1]) @ ground:.4f}")
print(f"   in the diagonal singlet-pair state: P(12 and 34 both singlets) = {vd @ sing(x_part[0]) @ sing(x_part[1]) @ vd:.4f}, P(23 and 14 both singlets) = {vd @ sing(y_part[0]) @ sing(y_part[1]) @ vd:.4f}")
print("   on the code space the two pairs of a setting always agree: P(12 singlet, 34 not) =", round(float(np.abs(code.conj().T @ sing(x_part[0]) @ (np.eye(16) - sing(x_part[1])) @ code).max()), 12))

print("\nL. A STAR CAN BE CALIBRATED WITH ITS OWN THREE PAIRS")
# Claim: for every unit direction m in the signal plane,   1/2 + G_star(m)/6  <=  3/4 + (S12 + S13 + S14)/12   as operators on all 16 dimensions.
# Consequence: a device without quantum memory scores at most 1 - (q1 + q2 + q3)/6 on a star, q_a = fraction of singlet outcomes at setting a.
tstar = sum(S[e] for e in star)
def slack(mu, grid=7200):
    return max(np.linalg.eigvalsh(0.5 * np.eye(16) + sum((np.cos(th - 2 * np.pi * a / 3)) * (-S[star[a]]) for a in range(3)) / 6 - mu * tstar).max()
               for th in np.linspace(0, 2 * np.pi, grid, endpoint=False))
# the directions: m at angle th from the first axis has m.n_a = cos(th - 2 pi a/3) in the frame (e1, e2) used above
assert np.allclose([n[a] @ (np.cos(0.3) * e1 + np.sin(0.3) * e2) for a in range(3)], [np.cos(0.3 - 2 * np.pi * a / 3) for a in range(3)]) or \
       np.allclose([n[a] @ (np.cos(0.3) * e1 + np.sin(0.3) * e2) for a in range(3)], [np.cos(0.3 + 2 * np.pi * a / 3) for a in range(3)])
print(f"   largest eigenvalue of 1/2 + G/6 - t/12 over 7,200 directions: {slack(1 / 12):.12f}   (claim: exactly 3/4)")
print("   the multiplier 1/12 is the only one that works:", {f"{mu:.4f}": float(round(slack(mu, 720), 6)) for mu in (1 / 12 - 0.01, 1 / 12 - 0.001, 1 / 12, 1 / 12 + 0.001, 1 / 12 + 0.01)})
print("   t = S12 + S13 + S14 on total spin 0, 1, 2:", [sorted({abs(float(v)) if abs(v) < 1e-9 else float(v) for v in np.round(np.linalg.eigvalsh(V[:, np.isclose(w, val)].conj().T @ tstar @ V[:, np.isclose(w, val)]), 6)}) for val in (0, 2, 6)])
pooled = np.zeros((16, 16), complex)
for a in range(3):
    Ga = sum((n[a] @ n[b]) * (-S[star[b]]) for b in range(3)); ww, vv = np.linalg.eigh(Pj[1] @ Ga @ Pj[1]); pooled += np.outer(vv[:, -1], vv[:, -1].conj()) / 3
q = [float(np.trace(pooled @ (np.eye(16) - S[e]) / 2).real) for e in star]
print(f"   the optimal attack of the star: singlet fractions at the three settings {np.round(q, 6)} (any code-space output: sum exactly 3/2); bound 1 - sum/6 = {1 - sum(q) / 6:.6f} >= its score 0.781023")
rng2 = np.random.default_rng(11); worst = -1.0
for _ in range(4000):
    th = rng2.uniform(0, 2 * np.pi); v = rng2.standard_normal(16) + 1j * rng2.standard_normal(16); v /= np.linalg.norm(v)
    O = 0.5 * np.eye(16) + sum((np.cos(th - 2 * np.pi * a / 3)) * (-S[star[a]]) for a in range(3)) / 6
    worst = max(worst, float((v.conj() @ O @ v).real - (0.75 + (v.conj() @ tstar @ v).real / 12)))
print(f"   4,000 random outputs and directions: largest (score - bound) = {worst:.6f}  (never positive)")
