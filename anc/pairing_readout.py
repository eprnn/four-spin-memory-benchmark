"""Four-spin comparison with and without checking the receiver's total spin."""
from itertools import combinations, permutations
import numpy as np


I = np.eye(2)
X = np.fliplr(I)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1., -1.])
TOL = 1e-11


def check(actual, expected):
    np.testing.assert_allclose(actual, expected, atol=TOL, rtol=0)


def permutation(order):
    return np.eye(16).reshape((2,)*8).transpose(tuple(order)+(4, 5, 6, 7)).reshape(16, 16)


def on_site(op, i):
    out = np.array([[1.]])
    for site in range(4):
        out = np.kron(out, op if site == i else I)
    return out


def score(code, qubit_projections, physical_yes, instrument, outputs, validate):
    code_space = code @ code.T
    success = 0.
    for q, yes in zip(qubit_projections, physical_yes):
        for state, test in ((q, yes), (I-q, np.eye(16)-yes)):
            if validate:
                test = code_space @ test @ code_space
            for outcome, output in zip(instrument, outputs):
                success += np.trace(outcome @ state)*np.vdot(output, test @ output).real/6
    return success.real


def main():
    singlet = np.array([0, 1, -1, 0])/np.sqrt(2)
    first = np.kron(singlet, singlet)
    second = permutation((0, 2, 1, 3)) @ first
    other = second - first*np.dot(first, second)
    code = np.column_stack([first, other/np.linalg.norm(other)])
    check(code.T @ code, I)
    spin_squared = np.zeros((16, 16), complex)
    for op in (X, Y, Z):
        generator = sum(on_site(op, i) for i in range(4))/2
        check(generator @ code, 0)
        spin_squared += generator @ generator
    check(np.linalg.eigvalsh(spin_squared), [0]*2+[2]*9+[6]*5)
    yes = []
    for j in range(1, 4):
        order = list(range(4))
        order[0], order[j] = order[j], order[0]
        yes.append((np.eye(16)-permutation(order))/2)
    qs = [code.T @ item @ code for item in yes]
    for q in qs:
        check(q @ q, q)
        check(np.trace(q), 1)
    check([[np.trace(q @ v) for v in qs] for q in qs], .75*np.eye(3)+.25)
    axes = np.array([[np.trace(q @ sigma).real for sigma in (X,Y,Z)] for q in qs])
    check(np.linalg.eigvalsh(axes.T @ axes/3), [0, .5, .5])
    check(np.linalg.eigvalsh(axes[:2].T @ axes[:2]/2), [0, .25, .75])
    ports = [permutation(p) for p in permutations(range(4))]
    for i in range(2):
        for j in range(2):
            unit = np.outer(code[:, i], code[:, j])
            check(sum(u @ unit @ u.T for u in ports)/24, (code @ code.T)*(i == j)/2)

    instrument = [2*q/3 for q in qs]
    check(sum(instrument), I)
    ideal_outputs = [code @ np.linalg.eigh(q)[1][:, -1] for q in qs]
    check(score(code, qs, yes, instrument, ideal_outputs, True), .75)

    # Return one of three spin-1 outputs chosen by a purely classical trine result.
    # The attacked outputs still have two up spins, just like all valid inputs.
    tagged = [i for i in range(16) if i.bit_count() == 2]
    outputs = []
    for axis in axes:
        observable = sum(c*(2*p-np.eye(16)) for c,p in zip(axes @ axis, yes))
        eig, vec = np.linalg.eigh(observable[np.ix_(tagged, tagged)])
        check(eig[-1], (1+np.sqrt(33))/4)
        out = np.zeros(16)
        out[tagged] = vec[:, -1]
        check(spin_squared @ out, 2*out)
        outputs.append(out)
    unchecked = score(code, qs, yes, instrument, outputs, False)
    check(unchecked, .5+(1+np.sqrt(33))/24)
    check(score(code, qs, yes, instrument, outputs, True), 0)

    # The spin-sector calibration uses independent settings on representative trials.
    all_swaps = np.zeros((16, 16))
    for i, j in combinations(range(4), 2):
        order = list(range(4))
        order[i], order[j] = order[j], order[i]
        all_swaps += permutation(order)
    check(spin_squared, all_swaps)
    spin_two = np.zeros(16)
    spin_two[tagged] = 1/np.sqrt(6)  # Permutation-symmetric, with two up spins.
    check(spin_squared @ spin_two, 6*spin_two)
    strategies = [ideal_outputs, outputs, [spin_two]*3]
    scores = [score(code, qs, yes, instrument, out, False) for out in strategies]
    check(scores, [.75, unchecked, .5])
    sector_means = [np.mean([np.vdot(v, all_swaps @ v).real for v in out])
                    for out in strategies]
    check(sector_means, [0, 2, 6])
    for a in range(11):
        for b in range(11-a):
            masses = np.array([a, b, 10-a-b])/10
            mean = masses @ sector_means
            ceiling = (scores[0]+(scores[1]-scores[0])*mean/2 if mean <= 2
                       else scores[1]+(scores[2]-scores[1])*(mean-2)/4)
            assert masses @ scores <= ceiling+TOL
            if masses[2] == 0 or masses[0] == 0:
                check(masses @ scores, ceiling)

    # A finite rational-probability strategy exceeding 3/4 also exists.
    rational_outputs = []
    for j in (1, 2, 3):
        v = np.ones(4)
        v[0], v[j] = 4, -6
        out = np.zeros(16)
        for word in tagged:
            occupied = [k for k, bit in enumerate(f"{word:04b}") if bit == "1"]
            out[word] = v[occupied].sum()
        rational_outputs.append(out/np.linalg.norm(out))
    check(score(code, qs, yes, instrument, rational_outputs, False), 253/324)

    # Verify the characteristic polynomial on the one-up block and full spectrum
    # for arbitrary directions in the measurement plane.
    one_up = [i for i in range(16) if i.bit_count() == 1]
    perp = np.cross([0., 1., 0.], axes[0])
    for phi in np.linspace(0, 2*np.pi, 181):
        direction = np.cos(phi)*axes[0] + np.sin(phi)*perp
        weights = axes @ direction
        observable = sum(c*(2*p-np.eye(16)) for c,p in zip(weights, yes))
        check(np.poly(observable[np.ix_(one_up, one_up)]),
              [1, 0, -9/4, -4*np.prod(weights), 0])
        max_eval = np.linalg.eigvalsh(observable)[-1]
        assert max_eval <= (1+np.sqrt(33))/4+TOL
    print(f"Singlet-validated score .750000; unchecked exact optimum {unchecked:.8f}.")
    print("All collective generators act trivially. Erasure of site labels depolarizes the code.")


if __name__ == "__main__":
    main()
