import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Explicit real amplitudes for the paper's signed swaps on the full four-bit basis.
Real amplitudes also specify complex kets by scalar inclusion. This file verifies
eigenvalues, permuted output branches, trine measurement forms, and the score
calculation using the paper’s conditional score formula. It does not derive that
formula, certify a spectral upper bound, or formalize density operators or channels. -/
namespace FourSpin.Witness
noncomputable section

abbrev Wave := Bool → Bool → Bool → Bool → ℝ

/-- Embed the ordered one-excitation amplitudes in the sixteen computational kets. -/
def single (a b c d : ℝ) : Wave
  | true, false, false, false => a
  | false, true, false, false => b
  | false, false, true, false => c
  | false, false, false, true => d
  | _, _, _, _ => 0

/-- Weighted signed transpositions of sites 12, 13, 14. -/
def star (a b c : ℝ) (x : Wave) : Wave := fun i j k l =>
  -a * x j i k l - b * x k j i l - c * x l j k i

/-- Weighted signed transpositions of sites 12, 13, 23. -/
def triangle (a b c : ℝ) (x : Wave) : Wave := fun i j k l =>
  -a * x j i k l - b * x k j i l - c * x i k j l

def starValue : ℝ := (1 + Real.sqrt 33) / 4

theorem starValue_quadratic : starValue ^ 2 = starValue / 2 + 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 33)
  unfold starValue
  nlinarith only [hs]

def starBranch1 : Wave := single (2 * starValue + 1) (-2 * starValue - 3) 1 1
def starBranch2 : Wave := single (2 * starValue + 1) 1 (-2 * starValue - 3) 1
def starBranch3 : Wave := single (2 * starValue + 1) 1 1 (-2 * starValue - 3)
def triangleBranch : Wave := single 1 (-1) 0 0

theorem starBranch1_nonzero : starBranch1 ≠ 0 := by
  intro h
  have hh := congrFun (congrFun (congrFun (congrFun h false) false) true) false
  norm_num [starBranch1, single, Pi.zero_apply] at hh

theorem starBranch2_nonzero : starBranch2 ≠ 0 := by
  intro h
  have hh := congrFun (congrFun (congrFun (congrFun h false) true) false) false
  norm_num [starBranch2, single, Pi.zero_apply] at hh

theorem starBranch3_nonzero : starBranch3 ≠ 0 := by
  intro h
  have hh := congrFun (congrFun (congrFun (congrFun h false) true) false) false
  norm_num [starBranch3, single, Pi.zero_apply] at hh

theorem triangleBranch_nonzero : triangleBranch ≠ 0 := by
  intro h
  have hh := congrFun (congrFun (congrFun (congrFun h true) false) false) false
  norm_num [triangleBranch, single, Pi.zero_apply] at hh

theorem starBranch1_eigen : star 1 (-1/2) (-1/2) starBranch1 =
    fun i j k l => starValue * starBranch1 i j k l := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp only [star, starBranch1, single] <;> nlinarith only [starValue_quadratic]

theorem starBranch2_eigen : star (-1/2) 1 (-1/2) starBranch2 =
    fun i j k l => starValue * starBranch2 i j k l := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp only [star, starBranch2, single] <;> nlinarith only [starValue_quadratic]

theorem starBranch3_eigen : star (-1/2) (-1/2) 1 starBranch3 =
    fun i j k l => starValue * starBranch3 i j k l := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp only [star, starBranch3, single] <;> nlinarith only [starValue_quadratic]

theorem triangleBranch_eigen : triangle 1 (-1/2) (-1/2) triangleBranch =
    fun i j k l => (3/2 : ℝ) * triangleBranch i j k l := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [triangle, triangleBranch, single]

def triangleBranch2 : Wave := single 1 0 (-1) 0
def triangleBranch3 : Wave := single 0 1 (-1) 0

theorem triangleBranch2_eigen : triangle (-1/2) 1 (-1/2) triangleBranch2 =
    fun i j k l => (3/2 : ℝ) * triangleBranch2 i j k l := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [triangle, triangleBranch2, single]

theorem triangleBranch3_eigen : triangle (-1/2) (-1/2) 1 triangleBranch3 =
    fun i j k l => (3/2 : ℝ) * triangleBranch3 i j k l := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [triangle, triangleBranch3, single]

theorem triangleBranch2_nonzero : triangleBranch2 ≠ 0 := by
  intro h
  have hh := congrFun (congrFun (congrFun (congrFun h true) false) false) false
  norm_num [triangleBranch2, single, Pi.zero_apply] at hh

theorem triangleBranch3_nonzero : triangleBranch3 ≠ 0 := by
  intro h
  have hh := congrFun (congrFun (congrFun (congrFun h false) true) false) false
  norm_num [triangleBranch3, single, Pi.zero_apply] at hh

/-- Inner product on the one-excitation block. For the embedded kets the
twelve remaining summands of the full sixteen-dimensional product are zero. -/
def singleDot (x y : Wave) : ℝ :=
  x true false false false * y true false false false +
  x false true false false * y false true false false +
  x false false true false * y false false true false +
  x false false false true * y false false false true

theorem singleDot_pos (a b c d : ℝ)
    (h : single a b c d ≠ 0) : 0 < singleDot (single a b c d) (single a b c d) := by
  apply lt_of_not_ge
  intro hn
  change a*a + b*b + c*c + d*d ≤ 0 at hn
  have ha : a = 0 := by
    have hsq : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    exact pow_eq_zero hsq
  have hb : b = 0 := by
    have hsq : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    exact pow_eq_zero hsq
  have hc : c = 0 := by
    have hsq : c ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    exact pow_eq_zero hsq
  have hd : d = 0 := by
    have hsq : d ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    exact pow_eq_zero hsq
  apply h
  subst a b c d
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;> rfl

theorem single_expectation (x y : Wave) (e : ℝ) (hn : singleDot x x ≠ 0)
    (he : y = fun i j k l => e * x i j k l) : singleDot x y / singleDot x x = e := by
  apply (div_eq_iff hn).2
  rw [he]
  unfold singleDot
  ring

/-- The first, second, and third input effects are positive rank-one forms
with unit directions (1,0), (1/2,√3/2), and (1/2,-√3/2).
Their Bloch directions are the three directions of the paper's trine. -/
def trineEffect (a b u v : ℝ) : ℝ := (2 / 3) * (a * u + b * v)^2

theorem trineEffect_nonneg (a b u v : ℝ) : 0 ≤ trineEffect a b u v := by
  unfold trineEffect
  exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem trineEffect_complete (u v : ℝ) :
    trineEffect 1 0 u v +
    trineEffect (1/2) (Real.sqrt 3 / 2) u v +
    trineEffect (1/2) (-Real.sqrt 3 / 2) u v = u^2 + v^2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold trineEffect
  calc
    _ = u^2 + Real.sqrt 3 ^ 2 * v^2 / 3 := by ring
    _ = _ := by rw [hs]; ring

inductive TrineAxis
  | first | second | third
  deriving DecidableEq

def trineKet : TrineAxis → ℝ × ℝ
  | .first => (1, 0)
  | .second => (1/2, Real.sqrt 3 / 2)
  | .third => (1/2, -Real.sqrt 3 / 2)

def ketOverlap (a b : TrineAxis) : ℝ :=
  (trineKet a).1 * (trineKet b).1 + (trineKet a).2 * (trineKet b).2

/-- Twice the overlap probability of the positive input kets minus one
gives the signed coefficient of the corresponding receiver swap. -/
theorem trineSwap_coefficient (a b : TrineAxis) :
    2 * ketOverlap a b ^ 2 - 1 = if a = b then 1 else -1/2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hov : ketOverlap a b =
      if a = b then 1 else if (a = .second ∧ b = .third) ∨
        (a = .third ∧ b = .second) then -1/2 else 1/2 := by
    cases a <;> cases b <;>
      simp [ketOverlap, trineKet] <;> nlinarith only [hs]
  rw [hov]
  cases a <;> cases b <;> simp <;> norm_num

/-- Real and imaginary parts contribute independently to the positive
quadratic form of these real-coefficient effects on complex inputs. -/
theorem trineEffect_complex_complete (ur vr ui vi : ℝ) :
    (trineEffect 1 0 ur vr + trineEffect 1 0 ui vi) +
    (trineEffect (1/2) (Real.sqrt 3 / 2) ur vr +
      trineEffect (1/2) (Real.sqrt 3 / 2) ui vi) +
    (trineEffect (1/2) (-Real.sqrt 3 / 2) ur vr +
      trineEffect (1/2) (-Real.sqrt 3 / 2) ui vi) = ur^2 + vr^2 + ui^2 + vi^2 := by
  linarith only [trineEffect_complete ur vr, trineEffect_complete ui vi]

/-- Half the trace of each trine effect is 1/3, the branch weight used below. -/
theorem trineEffect_halfTrace (a : TrineAxis) :
    (trineEffect (trineKet a).1 (trineKet a).2 1 0 +
      trineEffect (trineKet a).1 (trineKet a).2 0 1) / 2 = 1/3 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  cases a <;> norm_num [trineEffect, trineKet] <;> nlinarith only [hs]

/-- Apply the paper's conditional score formula with three branches of
weight 1/3 and a common output expectation. -/
def branchAverage (e₁ e₂ e₃ : ℝ) : ℝ :=
  ((1/2 + e₁/6) + (1/2 + e₂/6) + (1/2 + e₃/6)) / 3

theorem starBranch_average :
    branchAverage starValue starValue starValue = 1/2 + (1 + Real.sqrt 33) / 24 := by
  unfold branchAverage starValue
  ring

theorem triangleBranch_average :
    branchAverage (3/2) (3/2) (3/2) = 3/4 := by
  norm_num [branchAverage]

theorem starOutput_score :
    branchAverage
      (singleDot starBranch1 (star 1 (-1/2) (-1/2) starBranch1) / singleDot starBranch1 starBranch1)
      (singleDot starBranch2 (star (-1/2) 1 (-1/2) starBranch2) / singleDot starBranch2 starBranch2)
      (singleDot starBranch3 (star (-1/2) (-1/2) 1 starBranch3) / singleDot starBranch3 starBranch3) = 1/2 + (1 + Real.sqrt 33) / 24 := by
  have h1 : singleDot starBranch1 (star 1 (-1/2) (-1/2) starBranch1) / singleDot starBranch1 starBranch1 = starValue :=
    single_expectation _ _ _
      (ne_of_gt (singleDot_pos _ _ _ _ starBranch1_nonzero)) starBranch1_eigen
  have h2 : singleDot starBranch2 (star (-1/2) 1 (-1/2) starBranch2) / singleDot starBranch2 starBranch2 = starValue :=
    single_expectation _ _ _
      (ne_of_gt (singleDot_pos _ _ _ _ starBranch2_nonzero)) starBranch2_eigen
  have h3 : singleDot starBranch3 (star (-1/2) (-1/2) 1 starBranch3) / singleDot starBranch3 starBranch3 = starValue :=
    single_expectation _ _ _
      (ne_of_gt (singleDot_pos _ _ _ _ starBranch3_nonzero)) starBranch3_eigen
  simpa only [h1, h2, h3] using starBranch_average

theorem triangleOutput_score :
    branchAverage
      (singleDot triangleBranch (triangle 1 (-1/2) (-1/2) triangleBranch) / singleDot triangleBranch triangleBranch)
      (singleDot triangleBranch2 (triangle (-1/2) 1 (-1/2) triangleBranch2) / singleDot triangleBranch2 triangleBranch2)
      (singleDot triangleBranch3 (triangle (-1/2) (-1/2) 1 triangleBranch3) / singleDot triangleBranch3 triangleBranch3) = 3/4 := by
  have h1 : singleDot triangleBranch (triangle 1 (-1/2) (-1/2) triangleBranch) / singleDot triangleBranch triangleBranch = (3/2 : ℝ) :=
    single_expectation _ _ _
      (ne_of_gt (singleDot_pos _ _ _ _ triangleBranch_nonzero)) triangleBranch_eigen
  have h2 : singleDot triangleBranch2 (triangle (-1/2) 1 (-1/2) triangleBranch2) / singleDot triangleBranch2 triangleBranch2 = (3/2 : ℝ) :=
    single_expectation _ _ _
      (ne_of_gt (singleDot_pos _ _ _ _ triangleBranch2_nonzero)) triangleBranch2_eigen
  have h3 : singleDot triangleBranch3 (triangle (-1/2) (-1/2) 1 triangleBranch3) / singleDot triangleBranch3 triangleBranch3 = (3/2 : ℝ) :=
    single_expectation _ _ _
      (ne_of_gt (singleDot_pos _ _ _ _ triangleBranch3_nonzero)) triangleBranch3_eigen
  simpa only [h1, h2, h3] using triangleBranch_average

#print axioms starBranch1_nonzero
#print axioms starBranch2_nonzero
#print axioms starBranch3_nonzero
#print axioms triangleBranch_nonzero
#print axioms triangleBranch2_nonzero
#print axioms triangleBranch3_nonzero
#print axioms singleDot_pos
#print axioms single_expectation
#print axioms starBranch1_eigen
#print axioms starBranch2_eigen
#print axioms starBranch3_eigen
#print axioms triangleBranch_eigen
#print axioms triangleBranch2_eigen
#print axioms triangleBranch3_eigen
#print axioms trineEffect_nonneg
#print axioms trineEffect_complete
#print axioms trineEffect_complex_complete
#print axioms trineEffect_halfTrace
#print axioms trineSwap_coefficient
#print axioms starBranch_average
#print axioms starOutput_score
#print axioms triangleOutput_score
#print axioms triangleBranch_average

end

end FourSpin.Witness
