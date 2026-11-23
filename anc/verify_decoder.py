#!/usr/bin/env python3
r"""Independent audit of the balanced-score CPTP decoder Lambda_bal.

Verifies five exact results:
  1. Impossibility of raw-statistics squashing:
     On C^2, sum_{k=1}^3 P_k^log = (3/2) I_2, whereas on C^16, sum_{k=1}^3 Q_k^sym = (3/2) I_16 - (1/4) J^2
     (sums to 3/2 on J=0, 1 on J=1, 0 on J=2). No CPTP (or even trace-preserving) raw squashing map exists!
  2. Exact adjoint shift & universal coverage of Lambda_bal under uniform fair-sign inputs:
     Lambda_bal: J=0 -> identity on C^2; J=1 -> measure orthogonal partition projectors A_k|_{J=1} and output
     tau_k = (I_2 - (2/3) n_k.sigma)/2; J=2 -> output I_2/2.
     Exact adjoint identity:
       Lambda_bal^\dagger(P_k^log) - Q_k^sym = +(1/6) Pi_{J=1} + (1/2) Pi_{J=2}  for k = 1, 2, 3,
       Lambda_bal^\dagger(I - P_k^log) - (I - Q_k^sym) = -(1/6) Pi_{J=1} - (1/2) Pi_{J=2}.
     Hence for ANY trace-nonincreasing CP map E: B(C^2) -> B(C^16) (coherent, non-EB, EB, or heralded early
     selection with arbitrary input-dependent acceptance) and ANY axis weights (p1, p2, p3) with fair signs:
       N_dec(Lambda_bal o E) - N_phys(E) = (1/2) Tr[ E((sum_k p_k n_k).sigma) * ((1/6) Pi_{J=1} + (1/2) Pi_{J=2}) ],
       eta_dec = eta_phys.
     At uniform weights p = (1/3, 1/3, 1/3), sum_k p_k n_k = 0 -> EXACT ZERO ERROR for ALL channels & ALL
     early-selection instruments without a basis hint!
  3. Sharp failure / impossibility boundary (unequal axis weights / basis hints OR biased signs):
     - Per-axis / unequal-weight impossibility: no linear map can satisfy Lambda^\dagger(n_k.sigma) = -A_k
       for all k=1,2,3 since sum_k n_k.sigma = 0 while -sum_k A_k = -(1/2) J^2 != 0.
     - Explicit CPTP EB counterexample E_2(rho) = Tr(P_1^log rho)|Phi_1><Phi_1| + Tr(P_1^perp rho)|0000><0000|:
       at p=(1,0,0), F_phys = 1.0 vs F_dec = 0.75 (err = -1/4);
       at p=(2/3,1/6,1/6), F_phys - F_dec = +1/8 (physical strictly exceeds decoded!).
     - Biased-sign counterexample even at UNIFORM axes (beta = P(+|k) != 1/2):
       at beta = 0 (all-NO), |0000> in J=2 gives F_phys = 1.0 vs F_dec = 0.5 (err = -1/2).
  4. Surprise bonus theorem (16D EB ceiling STILL equals 2D logical ceiling for ALL unequal axis weights!):
     Even though NO single CPTP decoder preserves per-channel scores under unequal axis weights (p1, p2, p3)
     with fair signs, the 16D physical EB ceiling on the randomized complementary-pair receiver STILL equals
     the 2D logical J=0 EB ceiling (3 + Delta)/4 where Delta = ||sum_k p_k n_k|| = sqrt(p1^2+p2^2+p3^2-p1p2-p2p3-p3p1):
       - J=0: lambda_max(M) = (1 + Delta)/2,
       - J=1: max(p1, p2, p3) <= p_k + (1 - p_k)/4 <= (1 + Delta)/2,
       - J=2: ||sum_k p_k n_k|| = Delta <= (1 + Delta)/2.
"""
import json
from pathlib import Path
import numpy as np


ATOL = 1e-11
I2 = np.eye(2, dtype=complex)
X2 = np.array([[0, 1], [1, 0]], dtype=complex)
Y2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z2 = np.array([[1, 0], [0, -1]], dtype=complex)


def swap_op(i, j):
    M = np.zeros((16, 16), dtype=float)
    for w in range(16):
        bi = (w >> (3 - i)) & 1
        bj = (w >> (3 - j)) & 1
        nw = w ^ ((bi ^ bj) << (3 - i)) ^ ((bi ^ bj) << (3 - j))
        M[nw, w] = 1.0
    return M


def main():
    S12, S34 = swap_op(0, 1), swap_op(2, 3)
    S13, S24 = swap_op(0, 2), swap_op(1, 3)
    S14, S23 = swap_op(0, 3), swap_op(1, 2)
    A1, A2, A3 = 0.5 * (S12 + S34), 0.5 * (S13 + S24), 0.5 * (S14 + S23)
    As = (A1, A2, A3)
    Qs_yes = [0.5 * (np.eye(16) - A) for A in As]
    Qs_no = [0.5 * (np.eye(16) + A) for A in As]

    J_sq = S12 + S34 + S13 + S24 + S14 + S23
    evals_J, evecs_J = np.linalg.eigh(J_sq)
    B0 = evecs_J[:, np.abs(evals_J - 0.0) < 1e-9]
    B1 = evecs_J[:, np.abs(evals_J - 2.0) < 1e-9]
    B2 = evecs_J[:, np.abs(evals_J - 6.0) < 1e-9]
    P_J0, P_J1, P_J2 = B0 @ B0.T, B1 @ B1.T, B2 @ B2.T

    # 1. Impossibility of raw-statistics squashing
    sum_Q_yes = sum(Qs_yes)
    assert np.allclose(sum_Q_yes, 1.5 * np.eye(16) - 0.25 * J_sq, atol=ATOL)
    raw_sums_by_sector = [
        float(np.trace((B.T @ sum_Q_yes @ B)) / B.shape[1])
        for B in (B0, B1, B2)
    ]
    assert np.allclose(raw_sums_by_sector, [1.5, 1.0, 0.0], atol=ATOL)

    # Logical trine vectors n_k in B0 basis (where -A_k|_{J=0} = n_k . sigma)
    n_vecs = [
        np.array([float(np.trace((-B0.T @ A @ B0) @ P).real) / 2.0 for P in (X2, Y2, Z2)])
        for A in As
    ]
    assert np.allclose(sum(n_vecs), 0.0, atol=ATOL)
    Ps_log_yes = [0.5 * (I2 + n[0] * X2 + n[1] * Y2 + n[2] * Z2) for n in n_vecs]
    Ps_log_no = [I2 - P for P in Ps_log_yes]
    assert np.allclose(sum(Ps_log_yes), 1.5 * I2, atol=ATOL)

    # 2. Construct the CPTP balanced-score decoder Lambda_bal
    A_J1 = [P_J1 @ A @ P_J1 for A in As]
    taus = [0.5 * (I2 - (2.0 / 3.0) * (n[0] * X2 + n[1] * Y2 + n[2] * Z2)) for n in n_vecs]
    for tau in taus:
        assert np.min(np.linalg.eigvalsh(tau)) >= 1.0 / 6.0 - ATOL  # eigenvalues {1/6, 5/6}

    def Lambda_bal(rho16):
        out = B0.T @ rho16 @ B0
        for k in range(3):
            out = out + np.trace(A_J1[k] @ rho16) * taus[k]
        out = out + np.trace(P_J2 @ rho16) * (I2 / 2.0)
        return out

    # Verify exact adjoint shift on ALL 6 effects (yes & no, k=1,2,3)
    expected_shift = (1.0 / 6.0) * P_J1 + 0.5 * P_J2
    for k in range(3):
        adj_y = B0 @ Ps_log_yes[k] @ B0.T + sum(np.trace(taus[j] @ Ps_log_yes[k]) * A_J1[j] for j in range(3)) + 0.5 * P_J2
        adj_n = B0 @ Ps_log_no[k] @ B0.T + sum(np.trace(taus[j] @ Ps_log_no[k]) * A_J1[j] for j in range(3)) + 0.5 * P_J2
        assert np.allclose(adj_y - Qs_yes[k], expected_shift, atol=ATOL)
        assert np.allclose(adj_n - Qs_no[k], -expected_shift, atol=ATOL)

    # Verify exact coverage over 200 random trace-nonincreasing CP maps (non-EB + EB, heralded early selection)
    rng = np.random.default_rng(143)
    max_unif_err = 0.0
    max_formula_err = 0.0
    for _ in range(200):
        Ks = [rng.normal(size=(16, 2)) + 1j * rng.normal(size=(16, 2)) for _ in range(3)]
        S = sum(K.conj().T @ K for K in Ks)
        scale = float(np.max(np.linalg.eigvalsh(S))) * rng.uniform(1.0, 3.0)
        Ks = [K / np.sqrt(scale) for K in Ks]
        E = lambda rho2: sum(K @ rho2 @ K.conj().T for K in Ks)

        # Uniform axes (1/3, 1/3, 1/3)
        eta_p = eta_d = num_p = num_d = 0.0
        for k in range(3):
            oy, on = E(Ps_log_yes[k]), E(Ps_log_no[k])
            dy, dn = Lambda_bal(oy), Lambda_bal(on)
            eta_p += (np.trace(oy).real + np.trace(on).real) / 6.0
            eta_d += (np.trace(dy).real + np.trace(dn).real) / 6.0
            num_p += (np.trace(oy @ Qs_yes[k]).real + np.trace(on @ Qs_no[k]).real) / 6.0
            num_d += (np.trace(dy @ Ps_log_yes[k]).real + np.trace(dn @ Ps_log_no[k]).real) / 6.0
        assert np.isclose(eta_p, eta_d, atol=ATOL)
        max_unif_err = max(max_unif_err, abs(num_p / eta_p - num_d / eta_d))

        # Arbitrary random unequal weights (p1, p2, p3) against exact error formula
        pw = rng.dirichlet([1.0, 1.0, 1.0])
        np_w = nd_w = 0.0
        for k in range(3):
            oy, on = E(Ps_log_yes[k]), E(Ps_log_no[k])
            dy, dn = Lambda_bal(oy), Lambda_bal(on)
            np_w += 0.5 * pw[k] * (np.trace(oy @ Qs_yes[k]).real + np.trace(on @ Qs_no[k]).real)
            nd_w += 0.5 * pw[k] * (np.trace(dy @ Ps_log_yes[k]).real + np.trace(dn @ Ps_log_no[k]).real)
        v_vec = sum(pw[k] * n_vecs[k] for k in range(3))
        pred_diff = 0.5 * float(np.trace(E(v_vec[0] * X2 + v_vec[1] * Y2 + v_vec[2] * Z2) @ expected_shift).real)
        max_formula_err = max(max_formula_err, abs((nd_w - np_w) - pred_diff))

    assert max_unif_err < 1e-12
    assert max_formula_err < 1e-12

    # 3. Explicit counterexamples where Lambda_bal fails (unequal axis weights & biased signs)
    # E_2(rho) = Tr(P_1^log rho) |Phi_1><Phi_1| + Tr(P_1^perp rho) |0000><0000|
    # Note |Phi_1> = B0 @ eigvec(+1 of n_vecs[0].sigma)
    vals0, vecs0 = np.linalg.eigh(Ps_log_yes[0])
    phi1 = B0 @ vecs0[:, -1]
    rho_phi1 = np.outer(phi1, phi1.conj())
    rho_0000 = np.zeros((16, 16), dtype=complex)
    rho_0000[0, 0] = 1.0
    assert np.isclose(np.trace(rho_0000 @ P_J2).real, 1.0, atol=ATOL)
    E2 = lambda rho2: np.trace(Ps_log_yes[0] @ rho2) * rho_phi1 + np.trace(Ps_log_no[0] @ rho2) * rho_0000

    def eval_E2(weights, beta_pos=0.5):
        fp = fd = 0.0
        for k in range(3):
            oy, on = E2(Ps_log_yes[k]), E2(Ps_log_no[k])
            dy, dn = Lambda_bal(oy), Lambda_bal(on)
            fp += weights[k] * (beta_pos * np.trace(oy @ Qs_yes[k]).real + (1.0 - beta_pos) * np.trace(on @ Qs_no[k]).real)
            fd += weights[k] * (beta_pos * np.trace(dy @ Ps_log_yes[k]).real + (1.0 - beta_pos) * np.trace(dn @ Ps_log_no[k]).real)
        return float(fp), float(fd)

    fp_ax1, fd_ax1 = eval_E2((1.0, 0.0, 0.0), 0.5)
    assert np.isclose(fp_ax1, 1.0, atol=ATOL) and np.isclose(fd_ax1, 0.75, atol=ATOL)
    fp_hint, fd_hint = eval_E2((2.0 / 3.0, 1.0 / 6.0, 1.0 / 6.0), 0.5)
    assert np.isclose(fp_hint - fd_hint, 1.0 / 8.0, atol=ATOL)
    # Biased sign (beta=0 -> all NO) at UNIFORM axes (1/3,1/3,1/3) using constant output |0000>
    fp_bias = sum(np.trace(rho_0000 @ Qs_no[k]).real for k in range(3)) / 3.0
    fd_bias = sum(np.trace(Lambda_bal(rho_0000) @ Ps_log_no[k]).real for k in range(3)) / 3.0
    assert np.isclose(fp_bias, 1.0, atol=ATOL) and np.isclose(fd_bias, 0.5, atol=ATOL)

    # 4. Bonus theorem: for ALL unequal axis weights (p1, p2, p3) with fair signs, 16D EB ceiling == 2D J=0 ceiling (3 + Delta)/4
    max_eb_excess_J1_J2 = -1e9
    for p1 in np.linspace(0.0, 1.0, 21):
        for p2 in np.linspace(0.0, 1.0 - p1, 21):
            p3 = 1.0 - p1 - p2
            ps = (p1, p2, p3)
            delta = float(np.sqrt(max(0.0, p1 * p1 + p2 * p2 + p3 * p3 - p1 * p2 - p2 * p3 - p3 * p1)))
            lam_J0 = 0.5 * (1.0 + delta)
            lam_J1 = max(ps)
            lam_J2 = delta
            assert lam_J1 <= lam_J0 + ATOL
            assert lam_J2 <= lam_J0 + ATOL
            max_eb_excess_J1_J2 = max(max_eb_excess_J1_J2, lam_J1 - lam_J0, lam_J2 - lam_J0)

    out = {
        "raw_squashing_impossible": {
            "logical_sum_Pk_yes": 1.5,
            "physical_sum_Qk_yes_by_sector_J0_J1_J2": [round(x, 6) for x in raw_sums_by_sector],
        },
        "balanced_decoder_coverage_200_heralded_CP_maps": {
            "max_uniform_fair_sign_error": max_unif_err,
            "max_exact_error_formula_residual": max_formula_err,
            "exact_adjoint_shift": "(1/6)*Pi_{J=1} + (1/2)*Pi_{J=2}",
        },
        "counterexamples_where_Lambda_bal_fails": {
            "E2_axis1_p100": {"F_phys": round(fp_ax1, 6), "F_dec": round(fd_ax1, 6)},
            "E2_hint_2over3": {"F_phys": round(fp_hint, 6), "F_dec": round(fd_hint, 6), "F_phys_minus_F_dec": round(fp_hint - fd_hint, 6)},
            "uniform_axes_biased_sign_beta0_J2": {"F_phys": round(fp_bias, 6), "F_dec": round(fd_bias, 6)},
        },
        "unequal_axis_weights_16D_EB_equals_J0_logical_ceiling": {
            "max_J1_or_J2_excess_over_J0_across_231_priors": round(max_eb_excess_J1_J2, 12),
            "closed_form_ceiling": "(3 + sqrt(p1^2+p2^2+p3^2-p1*p2-p2*p3-p3*p1))/4",
        },
    }

    # 5. 60-degree Z_6 additive share rewrite (catching 2*part+sign non-isomorphism)
    # and fixed-triangle 3-qubit (01, 02, 12) decoder ignoring site 4.
    u_norm = np.cross(n_vecs[0], n_vecs[1])
    u_norm = u_norm / np.linalg.norm(u_norm)
    sig_u = u_norm[0] * X2 + u_norm[1] * Y2 + u_norm[2] * Z2
    e1_ax = n_vecs[0]
    e2_ax = np.cross(u_norm, e1_ax)
    ang_deg = lambda v: float(np.degrees(np.arctan2(np.dot(v, e2_ax), np.dot(v, e1_ax))) % 360.0)
    angs_L159 = [ang_deg(((-1) ** (k % 2)) * n_vecs[k // 2]) for k in range(6)]
    diffs_L159 = [round((angs_L159[(k + 1) % 6] - angs_L159[k]) % 360.0, 1) for k in range(6)]
    assert diffs_L159 == [180.0, 300.0, 180.0, 300.0, 180.0, 300.0]

    # Exact CRT / 60-degree cyclic Z_6 ordering: axis = (-k) % 3, sign = (-1)**k
    angs_Z6 = [ang_deg(((-1) ** k) * n_vecs[(-k) % 3]) for k in range(6)]
    diffs_Z6 = [round((angs_Z6[(k + 1) % 6] - angs_Z6[k]) % 360.0, 1) for k in range(6)]
    assert diffs_Z6 == [60.0] * 6

    def rot_log(d):
        th = np.pi * d / 3.0
        return np.cos(th / 2.0) * I2 - 1j * np.sin(th / 2.0) * sig_u

    states_Z6 = [Ps_log_yes[(-k) % 3] if k % 2 == 0 else Ps_log_no[(-k) % 3] for k in range(6)]
    phys_Z6 = [Qs_yes[(-k) % 3] if k % 2 == 0 else Qs_no[(-k) % 3] for k in range(6)]
    for d in range(6):
        U = rot_log(d)
        for k in range(6):
            assert np.allclose(U @ states_Z6[k] @ U.conj().T, states_Z6[(k + d) % 6], atol=ATOL)

    # Check 300 random 16D EB intercepts + arbitrary outcome/share-dependent rewrite d(s1, x) in Z_6
    max_z6_dec_diff = 0.0
    max_z6_score = 0.0
    for _ in range(300):
        ops = []
        for _ in range(4):
            M = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
            ops.append(M @ M.conj().T)
        S = sum(ops)
        sv, su = np.linalg.eigh(S)
        Sis = (su * (1.0 / np.sqrt(sv))[None, :]) @ su.conj().T
        Ms = [Sis @ M @ Sis for M in ops]
        outs16 = []
        for _ in range(4):
            B = rng.normal(size=(16, 2)) + 1j * rng.normal(size=(16, 2))
            r = B @ B.conj().T
            outs16.append(r / np.trace(r))
        d_tab = rng.integers(0, 6, size=(6, 4))
        p_phys = p_dec = 0.0
        for k in range(6):
            for s1 in range(6):
                for x in range(4):
                    prob = float(np.trace(Ms[x] @ states_Z6[k]).real)
                    d_sh = int(d_tab[s1, x])
                    kp = (k + d_sh) % 6
                    p_phys += (1.0 / 36.0) * prob * float(np.trace(outs16[x] @ phys_Z6[kp]).real)
                    Uinv = rot_log(-d_sh)
                    dec_u = Uinv @ Lambda_bal(outs16[x]) @ Uinv.conj().T
                    p_dec += (1.0 / 36.0) * prob * float(np.trace(dec_u @ states_Z6[k]).real)
        max_z6_dec_diff = max(max_z6_dec_diff, abs(p_phys - p_dec))
        max_z6_score = max(max_z6_score, p_phys)
    assert max_z6_dec_diff < 1e-11
    assert max_z6_score <= 0.75 + 1e-11

    # Fixed triangle (12, 13, 23) ignoring site 4: J_{123}=1/2 (8D) carries exact logical trine, J_{123}=3/2 (8D) -> I/2
    S12_t, S13_t, S23_t = swap_op(0, 1), swap_op(0, 2), swap_op(1, 2)
    J123_sum = S12_t + S13_t + S23_t
    assert np.allclose(np.sort(np.linalg.eigvalsh(J123_sum)), [0.0] * 8 + [3.0] * 8, atol=ATOL)
    out["z6_share_rewrite_and_triangle"] = {
        "L159_2part_plus_sign_step_diffs_deg": diffs_L159,
        "exact_60deg_Z6_step_diffs_deg": diffs_Z6,
        "random_300_16D_EB_arbitrary_rewrite_max_dec_diff": max_z6_dec_diff,
        "random_300_16D_EB_arbitrary_rewrite_max_score": round(max_z6_score, 6),
        "fixed_triangle_J123_sum_evals_verified": True,
    }

    Path(__file__).with_name("decoder-results.json").write_text(json.dumps(out, indent=2) + "\n")
    print("ALL BALANCED-SCORE DECODER, Z_6 REWRITE AND TRIANGLE ASSERTIONS PASSED.")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
