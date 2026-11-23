import FourSpin.Input
import FourSpin.Score
import Mathlib.Data.Real.Sqrt

/-! The complex qubit POVM measuring the three positive trine directions, and the six
pure signal matrices on which its Born probabilities are evaluated. -/
namespace FourSpin.TrineMeasurement

open scoped BigOperators ComplexOrder
noncomputable section

def u : Fin 3 → ℝ := ![1, -1/2, -1/2]
def v : Fin 3 → ℝ := ![0, Real.sqrt 3/2, -(Real.sqrt 3/2)]

def logical (a : Fin 3) : Input.Qubit := Input.axis (u a) (v a)

def sign (positive : Bool) : ℝ := if positive then 1 else -1

def rho (positive : Bool) (a : Fin 3) : Input.Qubit :=
  Input.signal (sign positive) (u a) (v a)

def effect (a : Fin 3) : Input.Qubit := (2/3 : ℝ) • rho true a

theorem axes_overlap (i j : Fin 3) :
    u i * u j + v i * v j = Score.trineOverlap i j := by
  fin_cases i <;> fin_cases j <;> norm_num [u, v, Score.trineOverlap] <;>
    nlinarith only [Real.sq_sqrt (show 0 ≤ (3:ℝ) by norm_num)]

theorem axes_unit (a : Fin 3) : (u a)^2 + (v a)^2 = 1 := by
  simpa [sq, Score.trineOverlap] using axes_overlap a a

private theorem pure_gram (s d e : ℝ) (h : (s*d)^2+(s*e)^2=1) :
    (Input.signal s d e).conjTranspose * Input.signal s d e = Input.signal s d e := by
  have hh : (Input.signal s d e).conjTranspose = Input.signal s d e := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Input.signal, Matrix.conjTranspose_apply, Complex.star_def]
  rw [hh]
  have hc : ((s:ℂ)*(d:ℂ))^2 + ((s:ℂ)*(e:ℂ))^2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Input.signal, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | (solve | ring) | linear_combination hc / 4

theorem signal_psd (p : Bool) (a : Fin 3) : (rho p a).PosSemidef := by
  have hnorm : (sign p * u a)^2 + (sign p * v a)^2 = 1 := by
    cases p <;> simpa [sign] using axes_unit a
  have h := Matrix.posSemidef_conjTranspose_mul_self (rho p a)
  simpa only [rho, pure_gram _ _ _ hnorm] using h

theorem signal_trace_one (p : Bool) (a : Fin 3) : (rho p a).trace = 1 := by
  simp [rho, Input.signal, Matrix.trace, Fin.sum_univ_two]
  ring

theorem effect_psd (a : Fin 3) : (effect a).PosSemidef :=
  (signal_psd true a).smul (by norm_num : (0:ℝ) ≤ 2/3)

theorem povm_complete : (∑ a, effect a) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_three, Matrix.cons_val_two, effect, rho, sign, u, v, Input.signal,
      Matrix.smul_apply, Complex.real_smul, Matrix.one_apply] <;> ring

theorem rho_plus (a : Fin 3) : rho true a = (1/2 : ℝ) • (1 + logical a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho, sign, logical, Input.axis, Input.signal, Matrix.one_apply,
      Matrix.smul_apply, Complex.real_smul] <;> ring

theorem rho_minus (a : Fin 3) : rho false a = (1/2 : ℝ) • (1 - logical a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho, sign, logical, Input.axis, Input.signal, Matrix.one_apply,
      Matrix.smul_apply, Complex.real_smul] <;> ring

/-- Full complex trace, with the real Born value embedded in ℂ. -/
theorem born_trace (x a : Fin 3) (p : Bool) :
    (effect x * rho p a).trace = ((1/3 * (1 + sign p * Score.trineOverlap x a) : ℝ) : ℂ) := by
  rw [← axes_overlap]
  cases p <;> norm_num [effect, rho, sign, Input.signal, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.smul_apply, Complex.real_smul] <;> ring

theorem born_plus (x a : Fin 3) : Score.born (effect x) ((1/2:ℝ) • (1 + logical a)) =
    (1/3:ℝ) * (1 + Score.trineOverlap x a) := by
  rw [← rho_plus, Score.born, born_trace]
  simp [sign]

theorem born_minus (x a : Fin 3) : Score.born (effect x) ((1/2:ℝ) • (1 - logical a)) =
    (1/3:ℝ) * (1 - Score.trineOverlap x a) := by
  rw [← rho_minus, Score.born, born_trace]
  simp [sign, sub_eq_add_neg]

#print axioms signal_psd
#print axioms signal_trace_one
#print axioms effect_psd
#print axioms povm_complete
#print axioms born_trace
#print axioms born_plus
#print axioms born_minus

end
end FourSpin.TrineMeasurement
