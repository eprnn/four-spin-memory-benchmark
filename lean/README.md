# A Lean proof of the four-spin star–triangle theorem

This companion verifies Theorem 1 of Erno Pirinen’s *Star and Triangle Pairing Readouts for a Four-Spin Decoherence-Free Memory Benchmark*. Three equally likely settings each have two equally likely signs. A classical replacement measures one input qubit with a finite-outcome POVM and prepares a four-spin state based on the outcome. The receiver measures whether one specified spin pair is a singlet.

The [main theorem](FourSpin/Dichotomy.lean) proves that for each of the eight fixed wirings the greatest attainable mean match score is

- **Star.** The three measured pairs share a site. The maximum is $1/2+(1+\sqrt{33})/24$, approximately 78.1023%.
- **Triangle.** The pairs connect three sites. The maximum is $3/4$, or 75%.

Every positive, trace-one complex output matrix on the full 16-dimensional space is allowed. The proof gives an explicit three-outcome strategy attaining each maximum. The triangle witness differs from the example in the manuscript and attains the same score.

## Run the proof

Install Lean's toolchain manager following the [official installation instructions](https://lean-lang.org/install/). In this directory run

```sh
lake exe cache get
lake --wfail build
lake env lean FourSpin.lean
```

The project pins Lean 4.24.0 and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The main theorem prints its axioms during the build. The only three are `propext`, `Classical.choice` and `Quot.sound`. The kernel checks universal identities and inequalities and the attaining strategies. [Lean's proof validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

## What to inspect

1. [Benchmark](FourSpin/Benchmark.lean) defines a strategy, the physical pair effects, and the six-trial score. [Input](FourSpin/Input.lean) and [Score](FourSpin/Score.lean) derive its weighted sum from Born probabilities.
2. [Swaps](FourSpin/Swaps.lean) proves polynomial identities on the actual four-spin wavefunctions. [Ceilings](FourSpin/Ceilings.lean) bounds their eigenvalues. [PhysicalMatrix](FourSpin/PhysicalMatrix.lean) and [Expectation](FourSpin/Expectation.lean) extend the bounds to mixed states.
3. [TrineMeasurement](FourSpin/TrineMeasurement.lean) constructs a complete positive input measurement. [Attainment](FourSpin/Attainment.lean) constructs normalized positive replacement states and proves their exact scores. [Wiring](FourSpin/Wiring.lean) and [Relabel](FourSpin/Relabel.lean) carry those results to all eight fixed receivers.
4. [Encoding](FourSpin/Encoding.lean) constructs an explicit isometric map from the logical qubit to two physical singlet states and checks its action under all six pair readouts.

The proof assumes the six stated preparations, ideal pair effects, equal trial weights and a single available input copy. The formal strategy class quantifies over every finite number of outcomes. Experimental calibration, setting-dependent losses, prior art, and the manuscript’s other theorems require separate checks. Erno Pirinen directed the research. AI assistants developed and checked the Lean sources.
