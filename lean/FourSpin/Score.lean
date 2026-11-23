import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Operational score of the six fair prepare-and-test trials.

An outcome of the input measurement selects one replacement. Its output is
represented by the three Born probabilities for that replacement. The
reduction uses the stated input Born probabilities and a single output table
shared by both signal signs, as required for measure and prepare.
-/

namespace FourSpin.Score

open scoped BigOperators

noncomputable section

variable {X : Type*} [Fintype X]

/-- The score obtained by averaging the six conditional match probabilities.
For each input measurement outcome, the output makes a yes result with
probability q; a negative signal matches on its complementary result. -/
def matchScore (pPlus pMinus : X → Fin 3 → ℝ) (q : X → Fin 3 → ℝ) : ℝ :=
  (∑ a : Fin 3, ∑ x : X,
    (pPlus x a * q x a + pMinus x a * (1 - q x a))) / 6

/-- Branch score in terms of input Bloch overlaps and binary output biases. -/
def branch (c q : Fin 3 → ℝ) : ℝ :=
  1 / 2 + (∑ a : Fin 3, c a * (2 * q a - 1)) / 6

/-- Eq. (eb_cond) follows from the affine input Born rule and the output
complement rule, for any finite outcome space. -/
theorem matchScore_eq_weighted_branch (w : X → ℝ) (c q : X → Fin 3 → ℝ) :
    matchScore (fun x a => w x * (1 + c x a))
      (fun x a => w x * (1 - c x a)) q =
      ∑ x : X, w x * branch (c x) (q x) := by
  unfold matchScore
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  have h : (∑ a : Fin 3, (w x * (1 + c x a) * q x a +
      w x * (1 - c x a) * (1 - q x a))) =
      ∑ a : Fin 3, (w x + w x * (c x a * (2 * q x a - 1))) := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [branch]
  ring

/-- Nonnegative weights of total one turn a branch-wise upper bound into a
bound for the full experiment. -/
theorem weighted_upper (w b : X → ℝ) (B : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hn : ∑ x, w x = 1) (hb : ∀ x, b x ≤ B) :
    (∑ x, w x * b x) ≤ B := by
  calc
    (∑ x, w x * b x) ≤ ∑ x, w x * B :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hb x) (hw x)
    _ = B := by rw [← Finset.sum_mul, hn, one_mul]

/-- A normalized mixture of branches all attaining the bound attains the
same score. Zero-weight branches may be left arbitrary. -/
theorem weighted_attains (w b : X → ℝ) (B : ℝ)
    (hn : ∑ x, w x = 1) (hb : ∀ x, w x ≠ 0 → b x = B) :
    (∑ x, w x * b x) = B := by
  calc
    (∑ x, w x * b x) = ∑ x, w x * B := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : w x = 0
      · simp [h]
      · rw [hb x h]
    _ = B := by rw [← Finset.sum_mul, hn, one_mul]

/-- Starting from arbitrary nonnegative input Born tables with a
setting-independent midpoint for each outcome, recover the affine form.
Zero-weight outcomes have no effect. -/
theorem input_affine_decomposition (pPlus pMinus : X → Fin 3 → ℝ)
    (hpos : ∀ x a, 0 ≤ pPlus x a)
    (hneg : ∀ x a, 0 ≤ pMinus x a)
    (hmid : ∀ x a, pPlus x a + pMinus x a = pPlus x 0 + pMinus x 0)
    (hplus : ∑ x, pPlus x 0 = 1) (hminus : ∑ x, pMinus x 0 = 1) :
    ∃ (w : X → ℝ) (c : X → Fin 3 → ℝ),
      (∀ x, 0 ≤ w x) ∧ (∑ x, w x = 1) ∧
      (∀ x a, |c x a| ≤ 1) ∧
      (∀ x a, pPlus x a = w x * (1 + c x a)) ∧
      (∀ x a, pMinus x a = w x * (1 - c x a)) := by
  let w : X → ℝ := fun x => (pPlus x 0 + pMinus x 0) / 2
  let c : X → Fin 3 → ℝ := fun x a => (pPlus x a - pMinus x a) / (2 * w x)
  have hw : ∀ x, 0 ≤ w x := by
    intro x
    dsimp [w]
    linarith [hpos x 0, hneg x 0]
  have hmass : ∑ x, w x = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib, hplus, hminus]
    norm_num
  have hsum (x : X) (a : Fin 3) : pPlus x a + pMinus x a = 2 * w x := by
    rw [hmid]
    dsimp [w]
    ring
  have hdiff (x : X) (a : Fin 3) : 2 * w x * c x a = pPlus x a - pMinus x a := by
    by_cases hz : w x = 0
    · have hs := hsum x a
      rw [hz] at hs ⊢
      have hp : pPlus x a = 0 := by linarith [hpos x a, hneg x a]
      have hm : pMinus x a = 0 := by linarith [hpos x a, hneg x a]
      simp [hp, hm]
    · dsimp [c]
      field_simp [hz]
  refine ⟨w, c, hw, hmass, ?_, ?_, ?_⟩
  · intro x a
    by_cases hz : w x = 0
    · simp [c, hz]
    · have hd := hdiff x a
      have hs := hsum x a
      have hdenom : 0 < 2 * w x := mul_pos (by norm_num) (lt_of_le_of_ne (hw x) (Ne.symm hz))
      apply abs_le.mpr
      constructor
      · apply le_of_mul_le_mul_left _ hdenom
        nlinarith [hneg x a, hpos x a]
      · apply le_of_mul_le_mul_left _ hdenom
        nlinarith [hneg x a, hpos x a]
  · intro x a
    nlinarith [hsum x a, hdiff x a]
  · intro x a
    nlinarith [hsum x a, hdiff x a]

/-- The spectral support bound can be supplied separately for each branch.
This corollary states the consequent bound on the six raw match probabilities. -/
theorem matchScore_upper (w : X → ℝ) (c q : X → Fin 3 → ℝ) (B : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hn : ∑ x, w x = 1)
    (hb : ∀ x, branch (c x) (q x) ≤ B) :
    matchScore (fun x a => w x * (1 + c x a))
      (fun x a => w x * (1 - c x a)) q ≤ B := by
  rw [matchScore_eq_weighted_branch]
  exact weighted_upper w (fun x => branch (c x) (q x)) B hw hn hb

/-- If input probabilities are normalized separately on all six signals
and are affine with fixed weights, the weights have total one and the
weighted contrasts vanish for each setting. -/
theorem affine_normalization (w : X → ℝ) (c : X → Fin 3 → ℝ)
    (hp : ∀ a, ∑ x, w x * (1 + c x a) = 1)
    (hm : ∀ a, ∑ x, w x * (1 - c x a) = 1) :
    (∑ x, w x = 1) ∧ (∀ a, ∑ x, w x * c x a = 0) := by
  have splitPlus (a : Fin 3) : (∑ x, w x) + (∑ x, w x * c x a) = 1 := by
    simpa only [mul_add, mul_one, Finset.sum_add_distrib] using hp a
  have splitMinus (a : Fin 3) : (∑ x, w x) - (∑ x, w x * c x a) = 1 := by
    simpa only [mul_sub, mul_one, Finset.sum_sub_distrib] using hm a
  constructor
  · linarith [splitPlus 0, splitMinus 0]
  · intro a
    linarith [splitPlus a, splitMinus a]

/-- At an attaining mixture, the six-trial score equals the common
conditional optimum on all outcomes of positive weight. -/
theorem matchScore_attains (w : X → ℝ) (c q : X → Fin 3 → ℝ) (B : ℝ)
    (hn : ∑ x, w x = 1)
    (hb : ∀ x, w x ≠ 0 → branch (c x) (q x) = B) :
    matchScore (fun x a => w x * (1 + c x a))
      (fun x a => w x * (1 - c x a)) q = B := by
  rw [matchScore_eq_weighted_branch]
  exact weighted_attains w (fun x => branch (c x) (q x)) B hn hb


/-- The same real trace pairing models both the input measurement and the
output binary test. Only the real part is needed for probabilities. -/
def born {d : Type*} [Fintype d] (A B : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (A * B)).re

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An output of trace one has complementary yes and no probabilities. -/
theorem born_complement (σ M : Matrix n n ℂ)
    (hσ : (Matrix.trace σ).re = 1) :
    born σ (1 - M) = 1 - born σ M := by
  simp [born, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hσ]

/-- The signed binary effect has expectation twice the yes probability
minus one. -/
theorem born_signed_effect (σ M : Matrix n n ℂ)
    (hσ : (Matrix.trace σ).re = 1) :
    born σ ((2 : ℝ) • M - 1) = 2 * born σ M - 1 := by
  simp [born, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, hσ]

/-- The setting operator is the linear combination of signed effects
used in the branch formula. -/
theorem branch_eq_trace (σ : Matrix n n ℂ)
    (M : Fin 3 → Matrix n n ℂ) (c : Fin 3 → ℝ)
    (hσ : (Matrix.trace σ).re = 1) :
    branch c (fun a => born σ (M a)) =
      1 / 2 + born σ (∑ a, c a • ((2 : ℝ) • M a - 1)) / 6 := by
  have hlin : born σ (∑ a, c a • ((2 : ℝ) • M a - 1)) =
      ∑ a, c a * born σ ((2 : ℝ) • M a - 1) := by
    simp [born, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]
  simp only [branch, hlin, born_signed_effect _ _ hσ]

/-- The two signal density matrices average to the same operator on
every setting. The midpoint identity holds against every input effect. -/
theorem born_input_midpoint (E : Matrix (Fin 2) (Fin 2) ℂ)
    (L : Matrix (Fin 2) (Fin 2) ℂ) :
    born E ((1 / 2 : ℝ) • (1 + L)) + born E ((1 / 2 : ℝ) • (1 - L)) =
      (Matrix.trace E).re := by
  simp only [born, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
    Complex.smul_re, smul_eq_mul]
  ring


/-- The output density operator of a finite measure-and-prepare strategy
on a Hermitian input. Its weights are the real input Born probabilities. -/
def replace (E : X → Matrix (Fin 2) (Fin 2) ℂ)
    (σ : X → Matrix n n ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix n n ℂ :=
  ∑ x, born (E x) ρ • σ x

omit [DecidableEq n] in
/-- Expanding the output trace yields the classical mixture of conditional
output probabilities on each trial. -/
theorem born_replace (E : X → Matrix (Fin 2) (Fin 2) ℂ)
    (σ : X → Matrix n n ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (M : Matrix n n ℂ) :
    born (replace E σ ρ) M = ∑ x, born (E x) ρ * born (σ x) M := by
  simp only [replace, born, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, Complex.smul_re, smul_eq_mul]

/-- Uniform average of the six actual output traces of a strategy. -/
def matrixMatchScore (E : X → Matrix (Fin 2) (Fin 2) ℂ)
    (σ : X → Matrix n n ℂ)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (M : Fin 3 → Matrix n n ℂ) : ℝ :=
  (∑ a : Fin 3, (
    born (replace E σ ((1 / 2 : ℝ) • (1 + L a))) (M a) +
    born (replace E σ ((1 / 2 : ℝ) • (1 - L a))) (1 - M a))) / 6

/-- The six raw output traces give exactly the score of the corresponding
real probability tables. -/
theorem matrixMatchScore_eq_table (E : X → Matrix (Fin 2) (Fin 2) ℂ)
    (σ : X → Matrix n n ℂ)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (M : Fin 3 → Matrix n n ℂ)
    (hσ : ∀ x, (Matrix.trace (σ x)).re = 1) :
    matrixMatchScore E σ L M =
      matchScore (fun x a => born (E x) ((1 / 2 : ℝ) • (1 + L a)))
        (fun x a => born (E x) ((1 / 2 : ℝ) • (1 - L a)))
        (fun x a => born (σ x) (M a)) := by
  simp only [matrixMatchScore, matchScore, born_replace, born_complement _ _ (hσ _),
    Finset.sum_add_distrib]

/-- Normalization of measured input probabilities follows from the POVM
completeness equality and the trace of the input signal. -/
theorem born_input_sum (E : X → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hE : (∑ x, E x) = 1) :
    ∑ x, born (E x) ρ = (Matrix.trace ρ).re := by
  unfold born
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hE, Matrix.one_mul]

/-- Fixed input overlaps identify the weighted matrix score with the
expected signed setting operator for each replacement. This uses
input Born affine identities as hypotheses, as provided by a Bloch
representation of each POVM element. -/
theorem matrixMatchScore_eq_weighted_trace (E : X → Matrix (Fin 2) (Fin 2) ℂ)
    (σ : X → Matrix n n ℂ)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (M : Fin 3 → Matrix n n ℂ)
    (w : X → ℝ) (c : X → Fin 3 → ℝ)
    (hp : ∀ x a, born (E x) ((1 / 2 : ℝ) • (1 + L a)) = w x * (1 + c x a))
    (hm : ∀ x a, born (E x) ((1 / 2 : ℝ) • (1 - L a)) = w x * (1 - c x a))
    (hσ : ∀ x, (Matrix.trace (σ x)).re = 1) :
    matrixMatchScore E σ L M =
      ∑ x, w x * (1 / 2 + born (σ x) (∑ a, c x a • ((2 : ℝ) • M a - 1)) / 6) := by
  simp only [matrixMatchScore_eq_table _ _ _ _ hσ, hp, hm,
    matchScore_eq_weighted_branch, branch_eq_trace _ _ _ (hσ _)]

/-- At the three trine directions the diagonal overlap is one and the
two off-diagonal overlaps are minus one half. -/
def trineOverlap (x a : Fin 3) : ℝ :=
  if x = a then 1 else -(1 / 2)

/-- The three equally weighted trine outcomes give six valid probability
columns for the measurement in the attaining star strategy. -/
theorem trine_probability_columns :
    (∀ x a, 0 ≤ (1 / 3 : ℝ) * (1 + trineOverlap x a) ∧
             0 ≤ (1 / 3 : ℝ) * (1 - trineOverlap x a)) ∧
    (∀ a, (∑ x : Fin 3, (1 / 3 : ℝ) * (1 + trineOverlap x a)) = 1) ∧
    (∀ a, (∑ x : Fin 3, (1 / 3 : ℝ) * (1 - trineOverlap x a)) = 1) := by
  have hsum (a : Fin 3) : ∑ x : Fin 3, trineOverlap x a = 0 := by
    unfold trineOverlap
    calc
      (∑ x : Fin 3, if x = a then 1 else -(1 / 2 : ℝ)) =
          ∑ x : Fin 3, ((if x = a then (3 / 2 : ℝ) else 0) - 1 / 2) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : x = a <;> norm_num [h]
      _ = 0 := by
        simp [Finset.sum_sub_distrib]
        norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro x a
    by_cases h : x = a <;> norm_num [trineOverlap, h]
  · intro a
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hsum]
    norm_num
  · intro a
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    norm_num

/-- Once replacement states attain the chosen support values, the
normalized trine strategy attains their common score. -/
theorem trine_matchScore_attains (q : Fin 3 → Fin 3 → ℝ) (B : ℝ)
    (hb : ∀ x, branch (trineOverlap x) (q x) = B) :
    matchScore (fun x a => (1 / 3 : ℝ) * (1 + trineOverlap x a))
      (fun x a => (1 / 3 : ℝ) * (1 - trineOverlap x a)) q = B := by
  apply matchScore_attains (fun _ => (1 / 3 : ℝ)) trineOverlap q B
  · norm_num [Fin.sum_univ_three]
  · intro x _
    exact hb x


/-- An antipodal two-outcome measurement has opposite overlaps at each setting. -/
def antipodalOverlap (c : Fin 3 → ℝ) (x : Fin 2) (a : Fin 3) : ℝ :=
  if x = 0 then c a else -(c a)

/-- The equally weighted antipodal outcomes yield normalized probability
columns whenever the overlaps lie in the unit interval. -/
theorem antipodal_probability_columns (c : Fin 3 → ℝ) (hc : ∀ a, |c a| ≤ 1) :
    (∀ x a, 0 ≤ (1 / 2 : ℝ) * (1 + antipodalOverlap c x a) ∧
             0 ≤ (1 / 2 : ℝ) * (1 - antipodalOverlap c x a)) ∧
    (∀ a, (∑ x : Fin 2, (1 / 2 : ℝ) * (1 + antipodalOverlap c x a)) = 1) ∧
    (∀ a, (∑ x : Fin 2, (1 / 2 : ℝ) * (1 - antipodalOverlap c x a)) = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x a
    have h := abs_le.mp (hc a)
    by_cases hx : x = 0 <;> simp only [antipodalOverlap, hx, if_true, if_false] <;>
      constructor <;> linarith [h.1, h.2]
  · intro a
    rw [Fin.sum_univ_two]
    norm_num [antipodalOverlap]
    ring
  · intro a
    rw [Fin.sum_univ_two]
    norm_num [antipodalOverlap]
    ring

/-- Replacement states at the common branch optimum for an antipodal
input measurement attain that optimum in the complete experiment. -/
theorem antipodal_matchScore_attains (c : Fin 3 → ℝ) (q : Fin 2 → Fin 3 → ℝ)
    (B : ℝ) (hb : ∀ x, branch (antipodalOverlap c x) (q x) = B) :
    matchScore (fun x a => (1 / 2 : ℝ) * (1 + antipodalOverlap c x a))
      (fun x a => (1 / 2 : ℝ) * (1 - antipodalOverlap c x a)) q = B := by
  apply matchScore_attains (fun _ => (1 / 2 : ℝ)) (antipodalOverlap c) q B
  · norm_num [Fin.sum_univ_two]
  · intro x _
    exact hb x

end

end FourSpin.Score

#print axioms FourSpin.Score.matchScore_eq_weighted_branch
#print axioms FourSpin.Score.input_affine_decomposition
#print axioms FourSpin.Score.affine_normalization
#print axioms FourSpin.Score.matchScore_upper
#print axioms FourSpin.Score.matchScore_attains

#print axioms FourSpin.Score.branch_eq_trace
#print axioms FourSpin.Score.born_input_midpoint
#print axioms FourSpin.Score.trine_probability_columns
#print axioms FourSpin.Score.trine_matchScore_attains

#print axioms FourSpin.Score.matrixMatchScore_eq_table
#print axioms FourSpin.Score.born_input_sum
#print axioms FourSpin.Score.matrixMatchScore_eq_weighted_trace

#print axioms FourSpin.Score.antipodal_probability_columns
#print axioms FourSpin.Score.antipodal_matchScore_attains
