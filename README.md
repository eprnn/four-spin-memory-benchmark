# Four-spin quantum memory benchmark

Verification code for *Star and Triangle Pairing Readouts for a Four-Spin Decoherence-Free Memory Benchmark*, a research manuscript by Erno Pirinen.

Two ways of measuring pairs of spins agree on every valid encoded input. They give different upper bounds on the score of a classical device that measures its input and prepares a replacement state. When the measured pairs form a triangle, the optimal score is 75%. When all three pairs share a spin (a star), it is approximately 78.10%. These are theoretical bounds. The example trial counts are synthetic.

## Reproduce the main result

Use Python 3 with NumPy. From the repository root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install numpy
python anc/verify_pairing.py
```

Section B of the output evaluates all eight fixed wirings from the four-spin operators. The expected star and triangle values are approximately **0.78102344** and **0.75000000**, respectively. Keep Python assertions enabled when running the checks.

## Check the formal proof of Theorem 1

The [Lean companion](lean/README.md) proves the exact maximum classical score for all eight ideal fixed wirings and constructs strategies that attain it. It covers every finite-outcome measure-and-prepare strategy with a single input copy and permits arbitrary four-spin output states. The [main theorem](lean/FourSpin/Dichotomy.lean) states both attainability and the upper bound. Experimental calibration and the other results in the manuscript have separate checks.

With the Lean toolchain manager installed, run the following from the repository root.

```sh
cd lean
lake exe cache get
lake --wfail build
lake env lean FourSpin.lean
```

The project pins Lean 4.24.0 and the Mathlib revision used for verification.

## Reproduce the remaining calculations

```sh
python anc/pairing_readout.py
python anc/paired_score_decoder.py
python anc/verify_decoder.py
python anc/check_readout.py
```

- `pairing_readout.py` constructs a replacement strategy that attains the star bound and tests the spin-sector calibration.
- `paired_score_decoder.py` checks all eight fixed wirings, the score-preserving decoder, and the split preparation record.
- `verify_decoder.py` independently checks the decoder and writes `anc/decoder-results.json`.
- `check_readout.py` checks the routed pair measurement, the star witness and exact binomial tails. For the illustrative 1,540 matches in 2,000 triangle trials, it brackets the largest mean detector-error allowance compatible with the one-sided 5% test between 0.00398332760 and 0.00398332761. It also reconstructs the star bound from the published swap matrices in [Ćwikliński et al., Eq. (43)](https://arxiv.org/abs/1201.6077).

To regenerate the two manuscript figures, install Matplotlib and run the following commands. The resulting PDFs are written in `anc/`.

```sh
python -m pip install matplotlib
python anc/draw_wiring.py
python anc/draw_star_score.py
```

The checks and figures have been run with Python 3.14.10, NumPy 2.5.5 and Matplotlib 3.11.2.

## Contributions and reuse

Erno Pirinen initiated and directed the research. Gemini 4 Neon drafted the manuscript and independently checked the detector and decoder calculations. GPT-6.2 Astra derived the wiring bounds and decoder and integrated the calculations. Claude Fable developed the same-trial star witness and independently checked the derivations. Corrections, references to earlier work and independent replications are welcome.

The code is available under the [MIT License](LICENSE).
