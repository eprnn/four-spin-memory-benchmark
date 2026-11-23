import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The real-plane Bloch coordinates of a general positive complex qubit effect. -/
namespace FourSpin.Input

open scoped BigOperators ComplexOrder
noncomputable section

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

def weight (E : Qubit) : ℝ := ((E 0 0).re + (E 1 1).re) / 2
def zCoord (E : Qubit) : ℝ := ((E 0 0).re - (E 1 1).re) / 2
def xCoord (E : Qubit) : ℝ := (E 0 1).re

theorem weight_eq_trace (E : Qubit) : weight E = E.trace.re / 2 := by
  simp [weight, Matrix.trace, Fin.sum_univ_two]

private theorem diag_im {E : Qubit} (h : E.PosSemidef) (i : Fin 2) :
    (E i i).im = 0 := by
  have he : ((E i i).re : ℂ) = E i i := h.isHermitian.coe_re_apply_self i
  calc
    (E i i).im = ((E i i).re : ℂ).im := congrArg Complex.im he.symm
    _ = 0 := rfl

theorem weight_nonneg {E : Qubit} (h : E.PosSemidef) : 0 ≤ weight E := by
  have ht : 0 ≤ E.trace.re := (Complex.le_def.mp h.trace_nonneg).1
  simp [Matrix.trace, Fin.sum_univ_two] at ht
  unfold weight
  linarith

theorem effect_disk {E : Qubit} (h : E.PosSemidef) :
    zCoord E ^ 2 + xCoord E ^ 2 ≤ weight E ^ 2 := by
  have hd : 0 ≤ E.det.re := (Complex.le_def.mp h.det_nonneg).1
  rw [Matrix.det_fin_two, ← h.isHermitian.apply 1 0] at hd
  simp [Complex.mul_re, diag_im h] at hd
  unfold weight xCoord zCoord
  nlinarith [sq_nonneg (E 0 1).im]

/-- Division by zero gives the zero Bloch vector for a zero-weight outcome. -/
theorem normalized_disk {E : Qubit} (h : E.PosSemidef) :
    (zCoord E / weight E) ^ 2 + (xCoord E / weight E) ^ 2 ≤ 1 := by
  by_cases hw : weight E = 0
  · simp [hw]
  · rw [div_pow, div_pow, ← add_div, div_le_one (sq_pos_of_ne_zero hw)]
    exact effect_disk h

theorem normalized_reconstruct {E : Qubit} (h : E.PosSemidef) :
    weight E * (zCoord E / weight E) = zCoord E ∧
    weight E * (xCoord E / weight E) = xCoord E := by
  by_cases hw : weight E = 0
  · have hd := effect_disk h
    rw [hw] at hd
    have hz : zCoord E = 0 := by nlinarith [sq_nonneg (xCoord E), sq_nonneg (zCoord E)]
    have hx : xCoord E = 0 := by nlinarith [sq_nonneg (xCoord E), sq_nonneg (zCoord E)]
    simp [hw, hz, hx]
  · simp [mul_div_cancel₀, hw]

def axis (d e : ℝ) : Qubit := !![(d : ℂ), (e : ℂ); (e : ℂ), -(d : ℂ)]

/-- The entries are written over the reals so their conjugations are explicit. -/
def signal (s d e : ℝ) : Qubit :=
  !![((1+s*d)/2 : ℝ), (s*e/2 : ℝ); (s*e/2 : ℝ), ((1-s*d)/2 : ℝ)]

theorem signal_eq (s d e : ℝ) :
    signal s d e = (2 : ℂ)⁻¹ • ((1 : Qubit) + (s : ℂ) • axis d e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signal, axis, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

theorem born_signed {E : Qubit} (h : E.PosSemidef) (s d e : ℝ) :
    (E * signal s d e).trace.re =
      weight E + s * (zCoord E * d + xCoord E * e) := by
  have hoff : (E 1 0).re = (E 0 1).re := by
    rw [← h.isHermitian.apply 1 0]
    rfl
  simp [signal, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply,
    Complex.mul_re, weight, zCoord, xCoord, hoff]
  ring

theorem born_signed_complex {E : Qubit} (h : E.PosSemidef) (s d e : ℝ) :
    (E * signal s d e).trace =
      ((weight E + s * (zCoord E * d + xCoord E * e) : ℝ) : ℂ) := by
  apply Complex.ext
  · exact born_signed h s d e
  · have hoff : (E 1 0).im = -(E 0 1).im := by
      rw [← h.isHermitian.apply 1 0]
      rfl
    simp [signal, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply,
      Complex.mul_im, diag_im h, hoff]

/-- Normalized Bloch overlaps give the branch Born probabilities, including at
zero weight; specializing s to +1 or -1 gives the two benchmark inputs. -/
theorem born_normalized {E : Qubit} (h : E.PosSemidef) (s d e : ℝ) :
    (E * signal s d e).trace.re = weight E *
      (1 + s * ((zCoord E / weight E) * d + (xCoord E / weight E) * e)) := by
  rw [born_signed h]
  obtain ⟨hz, hx⟩ := normalized_reconstruct h
  linear_combination -s * d * hz - s * e * hx

theorem povm_weights_sum {X : Type*} [Fintype X] (E : X → Qubit)
    (h : ∑ x, E x = 1) : ∑ x, weight (E x) = 1 := by
  have diag (i : Fin 2) : ∑ x, ((E x) i i).re = 1 := by
    have he := congrArg (fun M : Qubit => (M i i).re) h
    simpa [Matrix.sum_apply, Complex.re_sum] using he
  simp only [weight, ← Finset.sum_div, Finset.sum_add_distrib, diag]
  norm_num

#print axioms weight_eq_trace
#print axioms weight_nonneg
#print axioms effect_disk
#print axioms normalized_disk
#print axioms normalized_reconstruct
#print axioms signal_eq
#print axioms born_signed
#print axioms born_signed_complex
#print axioms born_normalized
#print axioms povm_weights_sum

end
end FourSpin.Input
