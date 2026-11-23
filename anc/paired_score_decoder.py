"""Verify the single-copy pairing score decoder and two finite record routes."""
from fractions import Fraction
from itertools import combinations, product

import numpy as np

from pairing_readout import I, check, permutation


def swap(i, j):
    order = list(range(4))
    order[i], order[j] = order[j], order[i]
    return permutation(order)


def detector():
    """Build all receiver observables from 16-dimensional site permutations."""
    physical_i = np.eye(16)
    spin_squared = sum(swap(i, j) for i, j in combinations(range(4), 2))
    eigenvalues, eigenvectors = np.linalg.eigh(spin_squared)
    sectors = [eigenvectors[:, np.isclose(eigenvalues, j)] for j in (0, 2, 6)]
    code, spin_one, spin_two = sectors
    p1, p2 = spin_one @ spin_one.T, spin_two @ spin_two.T
    parts = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    physical = [-(swap(*left) + swap(*right))/2 for left, right in parts]
    logical = [code.T @ item @ code for item in physical]
    readouts = [-p1 @ item @ p1 for item in physical]
    check(sum(logical), np.zeros((2, 2)))
    check(sum(physical), -p1-3*p2)
    check(sum(readouts), p1)
    for effect, axis in zip(readouts, logical):
        check(effect @ effect, effect)
        check(np.trace(effect), 3)
        check(axis @ axis, I)

    def decode(state):
        output = code.T @ state @ code + np.trace(p2 @ state)*I/2
        for effect, axis in zip(readouts, logical):
            output = output + np.trace(effect @ state)*(I/2-axis/3)
        return output

    # Complete positivity, trace preservation and all three adjoint identities.
    units = np.eye(256).reshape(16, 16, 16, 16)
    blocks = np.array([[decode(unit) for unit in row] for row in units])
    choi = blocks.transpose(0, 2, 1, 3).reshape(32, 32)
    assert np.linalg.eigvalsh(choi).min() > -1e-11
    check(np.trace(blocks, axis1=2, axis2=3), physical_i)
    for axis, observable in zip(logical, physical):
        adjoint = np.trace(blocks @ axis, axis1=2, axis2=3).T
        check(adjoint, observable + p1/3 + p2)
    return code, p2, logical, physical, decode


def test_scores(code, p2, logical, physical, decode):
    rng = np.random.default_rng(85573)
    for k in range(64):
        # A 2 -> (16 x 3) isometry, followed by environmental trace or herald.
        raw = rng.normal(size=(48, 2)) + 1j*rng.normal(size=(48, 2))
        isometry = np.linalg.qr(raw)[0].reshape(3, 16, 2)
        retained = isometry[:1+k % 3]
        def channel(state):
            return sum(op @ state @ op.conj().T for op in retained)

        sums = np.zeros(2)
        acceptance = 0.
        for axis, observable in zip(logical, physical):
            for sign in (1, -1):
                out = channel((I+sign*axis)/2)
                prob = np.trace(out).real
                acceptance += prob/6
                scores = [np.trace(out @ observable).real,
                          np.trace(decode(out) @ axis).real]
                sums += (prob + sign*np.array(scores))/12
        check(sums[0]/acceptance, sums[1]/acceptance)

    # An early filter followed by separate normalization inside each source label.
    physical_means, logical_means = [], []
    for axis, observable in zip(logical, physical):
        for sign in (1, -1):
            state = (I+sign*axis)/2
            plus = np.trace(state @ (I+logical[0])/2)
            out = plus*p2/5 + (1-plus)*(code @ code.T)/6
            prob = np.trace(out)
            physical_means.append((1+sign*np.trace(out @ observable)/prob)/2)
            logical_means.append((1+sign*np.trace(decode(out) @ axis)/prob)/2)
    check(np.mean(physical_means), 29/60)
    check(np.mean(logical_means), 1/2)
    print("64 channels and early filters agree on pooled scores; separate label means give 29/60 and 1/2.")


def test_all_fixed_receivers(code, logical, repaired):
    matchings = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    triangles = []
    optimum = (1+np.sqrt(33))/4
    for choices in product(range(2), repeat=3):
        edges = [pair[side] for pair, side in zip(matchings, choices)]
        observables = [-swap(i, j) for i, j in edges]
        for obs, axis in zip(observables, logical):
            check(code.T @ obs @ code, axis)
        vertices = set(site for edge in edges for site in edge)
        triangle = len(vertices) == 3
        if triangle:
            triangles.append(observables)
        else:
            assert len(set.intersection(*(set(e) for e in edges))) == 1
        # The three logical direction cosines measured from the first trine axis.
        largest = 0.
        for angle in np.linspace(0, 2*np.pi, 73):
            weights = np.cos(angle+np.arange(3)*2*np.pi/3)
            operator = sum(w*obs for w, obs in zip(weights, observables))
            ev = np.linalg.eigvalsh(operator)
            largest = max(largest, ev[-1])
            if triangle:
                check(ev, [-1.5]*4 + [0.]*8 + [1.5]*4)
        check(largest, 1.5 if triangle else optimum)
    assert len(triangles) == 4
    check(np.mean(triangles, axis=0), repaired)

    # A known erased site carries no logical information even with a reference:
    # check the complementary channel on a complete logical operator basis.
    for site in range(4):
        for a, b in product(range(2), repeat=2):
            unit = np.outer(code[:, a], code[:, b]).reshape((2,)*8)
            order = [site] + [j for j in range(4) if j != site]
            matrix = unit.transpose(order+[4+j for j in order]).reshape(2,8,2,8)
            check(np.trace(matrix, axis1=1, axis2=3), I*(a == b)/2)
    print("All eight fixed receivers classified. Four triangles attain 75%; four stars attain 78.102344%.")
    print("The triangle mixture reproduces all three randomized binary observables. Each erased site has constant marginal.")


def test_share_rewrites(logical, physical, decode):
    states = [(I+(-1)**k*logical[k % 3])/2 for k in range(6)]
    check(sum((-1)**k*state for k, state in enumerate(states)), 0*I)
    rotations = []
    for direction in (-1, 1):
        angle = direction*np.pi/6
        u = np.array([[np.cos(angle), -np.sin(angle)], [np.sin(angle), np.cos(angle)]])
        if np.allclose(u @ states[0] @ u.T, states[1]):
            rotations = [np.linalg.matrix_power(u, d) for d in range(6)]
    assert len(rotations) == 6
    # Full score operator for arbitrary unnormalized input-to-output branches.
    # Check on the complete 16 x 16 matrix basis rather than a sample of devices.
    for d, rotation in enumerate(rotations):
        physical_game = np.zeros((32, 32))
        decoded_game = np.zeros((32, 32))
        for k, state in enumerate(states):
            target = (k+d) % 6
            check(rotation @ state @ rotation.T, states[target])
            test = (np.eye(16)+(-1)**target*physical[target % 3])/2
            decoded_test = np.array([[np.trace(states[target] @ decode(unit))
                                      for unit in row]
                                     for row in np.eye(256).reshape(16,16,16,16)]).T
            physical_game += np.kron(state.T, test)/6
            decoded_game += np.kron(state.T, decoded_test)/6
        check(physical_game, decoded_game)
    print("All six outcome-dependent additive share shifts preserve the complete game operator.")


def test_closed_record_sources(code, logical):
    # Two logical code blocks (incoming, successor). The wire swaps them.
    # A common-source copy of the classical label instead controls a fresh
    # preparation on the successor block and leaves the incoming state behind.
    blank = np.array([1., 0.])
    swap_blocks = np.eye(4).reshape(2, 2, 2, 2).transpose(1, 0, 2, 3).reshape(4, 4)
    number = np.diag([i.bit_count() for i in range(16)])
    check(number @ code, 2*code)
    for axis in logical:
        for sign in (1, -1):
            target = (I+sign*axis)/2
            desired = np.linalg.eigh(target)[1][:, -1]
            orthogonal = np.array([-desired[1], desired[0]])
            prepare = np.column_stack([desired, orthogonal])
            physical_gate = code @ prepare @ code.T + np.eye(16)-code @ code.T
            check(physical_gate.T @ physical_gate, np.eye(16))
            check(physical_gate @ number, number @ physical_gate)
            fork = np.kron(I, prepare)
            for source in (desired, orthogonal):
                incoming = np.kron(source, blank)
                for circuit, expected in ((swap_blocks, np.outer(source, source)),
                                          (fork, target)):
                    final = (circuit @ incoming).reshape(2, 2)
                    check(final.T @ final, expected)
    print("Both unitary routes give the same passive output in each label block at fixed bare excitation.")


def test_record_routes(logical):
    # Label k goes around the hexagon. The visible share on its own is uniform.
    hist = np.zeros((6, 6, 6), dtype=int)
    for label in range(6):
        for pad in range(6):
            hist[label, pad, (label-pad) % 6] += 1
    for marginal in (hist.sum(axis=1), hist.sum(axis=2)):
        check(marginal, np.ones((6, 6)))
    for label, first, second in np.argwhere(hist):
        assert (first+second) % 6 == label
    scores = {kind: [] for kind in ('wire', 'common cause', 'leaked basis')}
    for flip in (0, 1):
        successes = dict.fromkeys(scores, Fraction(0))
        for label, first, second in np.argwhere(hist):
            axis = logical[label % 3]
            sign = (-1)**int(label % 2)
            state = (I+sign*axis)/2
            signal = I-state if flip else state
            # A basis leak permits classical measurement and re-preparation.
            rewritten = sum(np.trace(signal @ effect)*effect for effect in (state, I-state))
            for kind, output in [('wire', signal), ('common cause', state), ('leaked basis', rewritten)]:
                if flip == 0:
                    check(output, state)  # Equal states imply equal probabilities for every final measurement.
                match = np.trace(state @ output)
                check(match, round(match))
                successes[kind] += Fraction(round(match), 36)
        for kind in scores:
            scores[kind].append(successes[kind])
    assert scores == {'wire': [1, 0], 'common cause': [1, 1], 'leaked basis': [1, 0]}
    print("All 36 share pairs checked. Original-record match without/with signal flip:", scores)


if __name__ == '__main__':
    enc, spin2, axes, swaps, decoder = detector()
    test_scores(enc, spin2, axes, swaps, decoder)
    test_all_fixed_receivers(enc, axes, swaps)
    test_closed_record_sources(enc, axes)
    test_record_routes(axes)
    test_share_rewrites(axes, swaps, decoder)
