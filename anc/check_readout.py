"""Check the proposed routed pair observable and the finite-sample example."""
from fractions import Fraction
from itertools import product
from math import comb

import numpy as np


def swap_matrix(first, second):
    bits = list(product((0, 1), repeat=4))
    indices = {state: i for i, state in enumerate(bits)}
    matrix = np.zeros((16, 16), dtype=int)
    for i, state in enumerate(bits):
        new = list(state)
        new[first], new[second] = state[second], state[first]
        matrix[indices[tuple(new)], i] = 1
    return matrix


def binomial_tail(n, successes, p):
    a, b = p.numerator, p.denominator
    numerator = sum(comb(n, k)*a**k*(b-a)**(n-k) for k in range(successes, n+1))
    return Fraction(numerator, b**n)


def check_cloning_paper_matrices():
    """Compare the published spin-one block (arXiv:1201.6077, Eq. 43) to physical swaps."""
    r2, r3, r6 = np.sqrt([2, 3, 6])
    published = np.array([
        np.diag([1, 1, -1]),
        [[1, 0, 0], [0, -1/2, -r3/2], [0, -r3/2, 1/2]],
        [[-1/3, -r2/3, -r6/3], [-r2/3, 5/6, -r3/6], [-r6/3, -r3/6, 1/2]],
    ])
    physical = np.array([swap_matrix(0, site) for site in (1, 2, 3)])
    # On the full space spin one has multiplicity three for each eigenvalue.
    # The spin-zero eigenvalues are +/-3/2 and the spin-two score operator is zero.
    for angle in np.linspace(0, 2*np.pi, 73):
        weights = -np.cos(angle + 2*np.pi*np.arange(3)/3)
        spectrum = np.linalg.eigvalsh(np.einsum("i,ijk->jk", weights, published))
        full = np.linalg.eigvalsh(np.einsum("i,ijk->jk", weights, physical))
        predicted = np.sort(np.r_[np.repeat(spectrum, 3), -1.5, 1.5, np.zeros(5)])
        assert np.allclose(predicted, full)
    aligned = -published[0] + (published[1] + published[2])/2
    root = np.linalg.eigvalsh(aligned)[-1]
    assert np.isclose(root, (1+np.sqrt(33))/4)
    print(f"Star match ceiling from published cloning matrices: {0.5+root/6:.9f}")


def check_star_record_witness():
    """Verify the Schur certificate exactly on rational points of the trine circle."""
    for numerator in range(-9, 10):
        for denominator in range(1, 6):
            t = Fraction(numerator, denominator)
            c = [(3-t*t)/(3+t*t), (t*t-3+6*t)/(2*(3+t*t)),
                 (t*t-3-6*t)/(2*(3+t*t))]
            b = [1+2*x for x in c]
            assert sum(b) == 3 and sum(x*x for x in b) == 9
            schur = 3-sum(x*x/(6-x) for x in b)
            assert schur >= 0
            if max(b) == 3:
                assert schur == 0
    # Enumerate the ordinary single-trial records: uniform axes make the mean
    # of (match + one half of the singlet outcome) equal F + sum(q_a)/6.
    records = [(axis, sign, yes) for axis in range(3) for sign in (-1, 1)
               for yes in (False, True)]
    weights = [i*i+1 for i in range(len(records))]
    for axis in range(3):
        total = sum(w for w, r in zip(weights, records) if r[0] == axis)
        for i, record in enumerate(records):
            if record[0] == axis:
                weights[i] = Fraction(weights[i], 3*total)
    match = sum(w for w, (_, sign, yes) in zip(weights, records) if yes == (sign==1))
    q = [3*sum(w for w, (a, _, yes) in zip(weights, records) if a == axis and yes)
         for axis in range(3)]
    statistic = sum(w*((yes == (sign==1))+Fraction(int(yes),2))
                    for w, (_, sign, yes) in zip(weights, records))
    assert statistic == match+sum(q)/6
    print("Same-record star witness: exact Schur checks and trial-score identity passed.")


def check_commitment_examples():
    """Counterexamples when the setting leaks or a quantum channel retains its flag."""
    eye = np.eye(2)
    x = np.array([[0, 1], [1, 0]])
    y = np.array([[0, -1j], [1j, 0]])
    z = np.diag([1, -1])
    angles = np.arange(6)*np.pi/3
    states = [(eye+np.cos(angle)*z+np.sin(angle)*x)/2 for angle in angles]
    # Measure the first axis. After disclosure accept only its two eigenstates.
    acceptance = sum(k % 3 == 0 for k in range(6))/6
    correct = sum(np.trace(rho @ rho).real for k, rho in enumerate(states)
                  if k % 3 == 0)/6
    assert np.isclose(acceptance, 1/3) and np.isclose(correct/acceptance, 1)
    # A fair half turn about Y, with the matching label rewrite, preserves each verdict.
    # Once the flag is discarded the spin channel equals measurement in the Y basis.
    y_projectors = [(eye+y)/2, (eye-y)/2]
    for row in range(2):
        for col in range(2):
            unit = np.zeros((2, 2))
            unit[row, col] = 1
            channel = (unit + y @ unit @ y)/2
            assert np.allclose(channel, sum(proj @ unit @ proj for proj in y_projectors))
    for k, rho in enumerate(states):
        for shift, rotation in [(0, eye), (3, y)]:
            output = rotation @ rho @ rotation.conj().T
            assert np.isclose(np.trace(output @ states[(k+shift) % 6]), 1)
    print("Late acceptance and flag-retaining counterexamples passed.")


def check_error_bounds():
    """Check actual and ideal scores of positive physical effects after early heralding."""
    eye = np.eye(16)
    swaps = [swap_matrix(0, j) for j in (1, 2, 3)]
    effects = [(eye-s)/2 for s in swaps]
    total_spin = sum(swap_matrix(i, j) for i in range(4) for j in range(i+1, 4))
    ev, vectors = np.linalg.eigh(total_spin)
    code = vectors[:, np.isclose(ev, 0)]
    positive = [code.T @ e @ code for e in effects]
    rng = np.random.default_rng(7043)
    for _ in range(40):
        # Use generic rotated noisy effects. Each lies between 0 and identity.
        noisy = []
        for e in effects:
            z = rng.normal(size=(16,16))+1j*rng.normal(size=(16,16))
            u = np.linalg.qr(z)[0]
            delta = rng.uniform(0, .14)
            noisy.append((1-delta)*e + delta*(u @ e @ u.conj().T))
        mean_error = np.mean([max(abs(np.linalg.eigvalsh(g-e))) for e,g in zip(effects,noisy)])
        raw = rng.normal(size=(48,2))+1j*rng.normal(size=(48,2))
        k = np.linalg.qr(raw)[0][:16]  # trace-nonincreasing CP branch
        acceptance = 0.
        match = np.zeros(2)
        singlet = np.zeros(2)
        for a, prepared_plus in enumerate(positive):
            for plus, rho in ((True, prepared_plus), (False, np.eye(2)-prepared_plus)):
                out = k @ rho @ k.conj().T
                accepted = np.trace(out).real/6
                acceptance += accepted
                for j, q in enumerate((effects[a], noisy[a])):
                    yes = np.trace(out @ q).real/6
                    singlet[j] += yes
                    match[j] += yes if plus else accepted-yes
        assert abs(match[0]-match[1]) <= acceptance*mean_error + 1e-12
        w = match + singlet/2
        assert abs(w[0]-w[1]) <= acceptance*1.5*mean_error + 1e-12
    print("Readout-error bounds passed for 40 physical measurements and early heralds.")


if __name__ == "__main__":
    # Swapping sites 1 and 2, followed by singlet/triplet readout on sites
    # 2 and 3, realizes the otherwise unavailable measurement on sites 1 and 3.
    route = swap_matrix(0, 1)
    twice_effect_23 = np.eye(16, dtype=int)-swap_matrix(1, 2)
    twice_effect_13 = np.eye(16, dtype=int)-swap_matrix(0, 2)
    assert np.array_equal(route.T @ twice_effect_23 @ route, twice_effect_13)
    check_cloning_paper_matrices()
    check_star_record_witness()
    check_commitment_examples()
    check_error_bounds()
    for ceiling in (Fraction(3, 4), Fraction(19, 25)):
        pval = binomial_tail(2000, 1540, ceiling)
        print(f"P(X >= 1540 | n = 2000, p = {ceiling}) = {float(pval):.9f}")

    # For this count, the binomial upper tail increases with the assumed ceiling.
    # Bracket its 5% crossing with exact rational arithmetic.
    p_low = Fraction("0.75398332760")
    p_high = Fraction("0.75398332761")
    assert binomial_tail(2000, 1540, p_low) < Fraction(1, 20)
    assert binomial_tail(2000, 1540, p_high) > Fraction(1, 20)
    print("For 1540/2000, the 5% crossing in mean effect error lies between "
          "0.00398332760 and 0.00398332761.")
