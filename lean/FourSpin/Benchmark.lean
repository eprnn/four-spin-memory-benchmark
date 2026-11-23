import FourSpin.Score
import FourSpin.PhysicalMatrix
import FourSpin.Input

namespace FourSpin.Benchmark

open Score PhysicalMatrix Spectral
open scoped BigOperators ComplexOrder

noncomputable section

/-- The two fixed pair readouts on the representative sets of sites. -/
inductive Geometry
  | star
  | triangle

def Geometry.pair : Geometry → Fin 3 → Index → Index
  | .star => ![swap12, swap13, swap14]
  | .triangle => ![swap12, swap13, swap23]

def Geometry.top : Geometry → ℝ
  | .star => starTop
  | .triangle => 3 / 2

def Geometry.ceiling (g : Geometry) : ℝ := 1 / 2 + g.top / 6

def singlet (g : Geometry) (a : Fin 3) : Matrix Index Index ℂ :=
  (1 / 2 : ℝ) • (1 - swapMatrix (g.pair a))

def coefficients (u v : ℝ) : Fin 3 → ℝ := ![u, axisB u v, axisC u v]

structure POVM (X : Type*) [Fintype X] where
  effect : X → Matrix (Fin 2) (Fin 2) ℂ
  positive : ∀ x, (effect x).PosSemidef
  complete : ∑ x, effect x = 1

structure Replacement (X : Type*) [Fintype X] where
  measurement : POVM X
  state : X → Matrix Index Index ℂ
  positive : ∀ x, (state x).PosSemidef
  normalized : ∀ x, (state x).trace = 1

theorem signed_singlet (g : Geometry) (a : Fin 3) :
    (2 : ℝ) • singlet g a - 1 = -swapMatrix (g.pair a) := by
  rw [singlet, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  abel

private theorem radial_signed_sum (g : Geometry) (r a b c u v : ℝ)
    (hsum : a + b + c = 0)
    (hu : u = r * a) (hv : axisB u v = r * b) (hc : axisC u v = r * c) :
    (∑ k, coefficients u v k • ((2 : ℝ) • singlet g k - 1)) =
      r • (match g with
      | .star => starMatrix a b
      | .triangle => triangleMatrix a b) := by
  have hc' : c = -(a + b) := by linarith
  have h₀ : coefficients u v 0 = u := rfl
  have h₁ : coefficients u v 1 = axisB u v := rfl
  have h₂ : coefficients u v 2 = axisC u v := rfl
  rw [hc'] at hc
  simp only [Fin.sum_univ_three, signed_singlet, h₀, h₁, h₂]
  rw [hc, hv, hu]
  cases g <;>
    simp only [Geometry.pair, starMatrix, triangleMatrix, signedSwapSum, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_neg, ← neg_smul, smul_add, smul_smul, mul_neg] <;> rfl

private theorem top_nonnegative (g : Geometry) : 0 ≤ g.top := by
  cases g
  · exact le_trans (by norm_num) (le_of_lt three_halves_lt_starTop)
  · norm_num [Geometry.top]

theorem disk_expectation_le (g : Geometry) (u v : ℝ) (hd : u^2 + v^2 ≤ 1)
    (ρ : Matrix Index Index ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) :
    born ρ (∑ k, coefficients u v k • ((2 : ℝ) • singlet g k - 1)) ≤ g.top := by
  obtain ⟨r, a, b, c, hr, hr₁, _, htr, hu, hv, hc⟩ := disk_decomposition u v hd
  rw [radial_signed_sum g r a b c u v htr.1 hu hv hc]
  have hop : born ρ (match g with
      | .star => starMatrix a b
      | .triangle => triangleMatrix a b) ≤ g.top := by
    cases g
    · exact star_expectation_le htr hρ ht
    · exact triangle_expectation_le htr hρ ht
  simp only [born, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hop ⊢
  exact (mul_le_mul_of_nonneg_left hop hr).trans
    (by simpa using mul_le_mul_of_nonneg_right hr₁ (top_nonnegative g))

private theorem trace_weight_sum {X : Type*} [Fintype X] (P : POVM X) :
    (∑ x, (P.effect x).trace.re / 2) = 1 := by
  rw [← Finset.sum_div, ← Complex.re_sum, ← Matrix.trace_sum, P.complete]
  norm_num [Matrix.trace, Fin.sum_univ_two]

/-- A finite strategy with planar Born data is bounded on the average of
the six equally likely signed input trials. -/
theorem score_le_of_planar {X : Type*} [Fintype X] (g : Geometry)
    (R : Replacement X) (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (u v : X → ℝ) (hd : ∀ x, u x ^ 2 + v x ^ 2 ≤ 1)
    (hw : ∀ x, 0 ≤ (R.measurement.effect x).trace.re / 2)
    (hp : ∀ x a, born (R.measurement.effect x) ((1 / 2 : ℝ) • (1 + L a)) =
      (R.measurement.effect x).trace.re / 2 * (1 + coefficients (u x) (v x) a))
    (hm : ∀ x a, born (R.measurement.effect x) ((1 / 2 : ℝ) • (1 - L a)) =
      (R.measurement.effect x).trace.re / 2 * (1 - coefficients (u x) (v x) a)) :
    matrixMatchScore R.measurement.effect R.state L (singlet g) ≤ g.ceiling := by
  have ht (x : X) : (R.state x).trace.re = 1 := by rw [R.normalized x]; simp
  rw [matrixMatchScore_eq_weighted_trace _ _ _ _ _ _ hp hm ht]
  apply weighted_upper _ _ _ hw (trace_weight_sum R.measurement)
  intro x
  have h := disk_expectation_le g (u x) (v x) (hd x) (R.state x) (R.positive x) (R.normalized x)
  unfold Geometry.ceiling
  linarith only [h]


/-- The three real-plane qubit observables for the six fair signs and settings. -/
def setting : Fin 3 → Input.Qubit :=
  ![Input.axis 1 0, Input.axis (-1 / 2) (Real.sqrt 3 / 2),
    Input.axis (-1 / 2) (-(Real.sqrt 3 / 2))]

def score {X : Type*} [Fintype X] (g : Geometry) (R : Replacement X) : ℝ :=
  matrixMatchScore R.measurement.effect R.state setting (singlet g)

/-- The effect weights are half their traces. -/
theorem weight_trace (E : Input.Qubit) : Input.weight E = E.trace.re / 2 :=
  Input.weight_eq_trace E

private theorem signal_observable (s d e : ℝ) :
    Input.signal s d e = (1 / 2 : ℝ) • ((1 : Input.Qubit) + s • Input.axis d e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Input.signal, Input.axis, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul] <;> ring

theorem born_setting (E : Input.Qubit) (h : E.PosSemidef) (a : Fin 3) :
    let u := Input.zCoord E / Input.weight E
    let v := Input.xCoord E / Input.weight E
    born E ((1 / 2 : ℝ) • (1 + setting a)) = Input.weight E * (1 + coefficients u v a) ∧
    born E ((1 / 2 : ℝ) • (1 - setting a)) = Input.weight E * (1 - coefficients u v a) := by
  dsimp only
  have hp (d e : ℝ) := Input.born_normalized h 1 d e
  have hm (d e : ℝ) := Input.born_normalized h (-1) d e
  simp only [signal_observable, one_smul, neg_one_smul, one_mul, neg_mul,
    ← sub_eq_add_neg] at hp hm
  fin_cases a <;>
    constructor <;>
    simp only [setting, coefficients, Matrix.cons_val_zero', Matrix.cons_val_succ', born, axisB, axisC]
  · convert hp 1 0 using 1; ring
  · convert hm 1 0 using 1; ring
  · convert hp (-1 / 2) (Real.sqrt 3 / 2) using 1; ring
  · convert hm (-1 / 2) (Real.sqrt 3 / 2) using 1; ring
  · convert hp (-1 / 2) (-(Real.sqrt 3 / 2)) using 1; ring
  · convert hm (-1 / 2) (-(Real.sqrt 3 / 2)) using 1; ring

/-- Every finite-outcome qubit measure-and-prepare strategy obeys the
representative star and triangle ceilings on its six actual Born trials. -/
theorem operational_ceilings {X : Type*} [Fintype X] (R : Replacement X) :
    score .star R ≤ 1 / 2 + (1 + Real.sqrt 33) / 24 ∧
    score .triangle R ≤ 3 / 4 := by
  let u x := Input.zCoord (R.measurement.effect x) / Input.weight (R.measurement.effect x)
  let v x := Input.xCoord (R.measurement.effect x) / Input.weight (R.measurement.effect x)
  have h (g : Geometry) : score g R ≤ g.ceiling := by
    unfold score
    apply score_le_of_planar g R setting u v
    · intro x
      exact Input.normalized_disk (R.measurement.positive x)
    · intro x
      rw [← weight_trace]
      exact Input.weight_nonneg (R.measurement.positive x)
    · intro x a
      rw [← weight_trace]
      exact (born_setting _ (R.measurement.positive x) a).1
    · intro x a
      rw [← weight_trace]
      exact (born_setting _ (R.measurement.positive x) a).2
  constructor
  · convert h .star using 1
    unfold Geometry.ceiling Geometry.top starTop
    ring
  · convert h .triangle using 1
    norm_num [Geometry.ceiling, Geometry.top]

#print axioms operational_ceilings

end

end FourSpin.Benchmark
