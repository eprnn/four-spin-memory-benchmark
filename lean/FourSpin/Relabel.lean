import FourSpin.Wiring
import FourSpin.Benchmark
import Mathlib.Analysis.Matrix.Order

open scoped ComplexOrder MatrixOrder
open Matrix
namespace FourSpin.Relabel
open Wiring

abbrev Index := Bool × Bool × Bool × Bool

def bits : Index ≃ Bits where
  toFun := fun (i,j,k,l) => ⟨i,j,k,l⟩
  invFun := fun s => (s.one,s.two,s.three,s.four)
  left_inv := by rintro ⟨i,j,k,l⟩; rfl
  right_inv := by rintro ⟨i,j,k,l⟩; rfl

def transform (w : Choice) (i : Index) := bits.symm (relabelBits (relabeling w) (bits i))

theorem transform_involutive (w : Choice) : Function.Involutive (transform w) := by
  rintro ⟨i,j,k,l⟩
  obtain ⟨axis,b,c⟩ := w
  cases axis <;> cases b <;> rfl

def equiv (w : Choice) : Index ≃ Index := (transform_involutive w).toPerm _

def swap (w : Choice) (axis : Axis) (i : Index) := bits.symm (swapBits (edge w axis) (bits i))

theorem intertwine (w : Choice) (axis : Axis) (i : Index) :
    equiv w (swap w axis i) = swap (representative w) axis (equiv w i) := by
  change bits.symm (relabelBits _ (bits (bits.symm _))) = bits.symm (swapBits _ (bits (bits.symm _)))
  simp only [Equiv.apply_symm_apply, relabel_swap_to_representative]

abbrev Operator := Matrix Index Index ℂ

noncomputable def pull (w : Choice) (M : Operator) := M.submatrix (equiv w) (equiv w)

theorem pull_twice (w : Choice) (M : Operator) : pull w (pull w M) = M := by
  ext i j
  change M (transform w (transform w i)) (transform w (transform w j)) = M i j
  rw [transform_involutive w i, transform_involutive w j]

theorem pull_psd (w : Choice) {M : Operator} (h : M.PosSemidef) : (pull w M).PosSemidef :=
  h.submatrix (equiv w)

theorem pull_trace (w : Choice) (M : Operator) : (pull w M).trace = M.trace :=
  (equiv w).sum_comp (fun i => M i i)

theorem pull_born (w : Choice) (ρ M : Operator) :
    ((pull w ρ) * (pull w M)).trace = (ρ * M).trace := by
  unfold pull
  rw [Matrix.submatrix_mul_equiv]
  exact pull_trace _ _

noncomputable def swapOperator (w : Choice) (axis : Axis) : Operator :=
  Matrix.of fun i j => if swap w axis i = j then 1 else 0

theorem pull_swap (w : Choice) (axis : Axis) :
    pull w (swapOperator w axis) = swapOperator (representative w) axis := by
  ext i j
  change (if swap w axis (equiv w i) = equiv w j then (1 : ℂ) else 0) =
    (if swap (representative w) axis i = j then 1 else 0)
  have hi : equiv w (equiv w i) = i := transform_involutive w i
  have hj : equiv w (equiv w j) = j := transform_involutive w j
  have hcond : swap w axis (equiv w i) = equiv w j ↔ swap (representative w) axis i = j := by
    rw [← (equiv w).injective.eq_iff, intertwine, hi, hj]
  simp only [hcond]

noncomputable def singlet (w : Choice) (axis : Axis) : Operator :=
  (1 / 2 : ℝ) • (1 - swapOperator w axis)

theorem pull_singlet (w : Choice) (axis : Axis) :
    pull w (singlet w axis) = singlet (representative w) axis := by
  ext i j
  have hval := congrFun (congrFun (pull_swap w axis) i) j
  change swapOperator w axis (equiv w i) (equiv w j) = _ at hval
  simp only [singlet, pull, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, Equiv.apply_eq_iff_eq, hval]

/-- One density reindexing works simultaneously for all three setting labels. -/
theorem representative_density (w : Choice) (ρ : Operator) (h : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    (pull w ρ).PosSemidef ∧ (pull w ρ).trace = 1 ∧
      ∀ axis, ((pull w ρ) * singlet (representative w) axis).trace =
        (ρ * singlet w axis).trace := by
  refine ⟨pull_psd w h, (pull_trace w ρ).trans htr, ?_⟩
  intro axis
  rw [← pull_singlet w axis]
  exact pull_born _ _ _

/-- The inverse relabeling sends every representative strategy back to the wiring,
preserving all three singlet probabilities, including for explicit attaining states. -/
theorem wiring_density (w : Choice) (ρ : Operator) (h : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (pull w ρ).PosSemidef ∧ (pull w ρ).trace = 1 ∧
      ∀ axis, ((pull w ρ) * singlet w axis).trace =
        (ρ * singlet (representative w) axis).trace := by
  refine ⟨pull_psd w h, (pull_trace w ρ).trans htr, ?_⟩
  intro axis
  have hborn := pull_born w (pull w ρ) (singlet w axis)
  rw [pull_twice, pull_singlet] at hborn
  exact hborn.symm

#print axioms representative_density
#print axioms wiring_density
open Benchmark

def axisOfFin : Fin 3 → Axis := ![Axis.a, Axis.b, Axis.c]

def geometry (w : Choice) : Geometry := if isStar w then .star else .triangle

theorem representative_singlet (w : Choice) (k : Fin 3) :
    singlet (representative w) (axisOfFin k) = Benchmark.singlet (geometry w) k := by
  unfold representative geometry
  split <;> fin_cases k <;> rfl

noncomputable def transport {X : Type*} [Fintype X] (w : Choice) (R : Replacement X) :
    Replacement X where
  measurement := R.measurement
  state x := pull w (R.state x)
  positive x := pull_psd w (R.positive x)
  normalized x := (pull_trace w _).trans (R.normalized x)

noncomputable def score {X : Type*} [Fintype X] (w : Choice) (R : Replacement X) : ℝ :=
  Score.matrixMatchScore R.measurement.effect R.state setting (fun k => singlet w (axisOfFin k))

/-- Equality of the actual six-trial scores under a common physical output permutation. -/
theorem representative_score {X : Type*} [Fintype X] (w : Choice) (R : Replacement X) :
    score w R = Benchmark.score (geometry w) (transport w R) := by
  have hρ (x : X) : (R.state x).trace.re = 1 := by rw [R.normalized]; rfl
  have ht (x : X) : ((transport w R).state x).trace.re = 1 := by
    rw [(transport w R).normalized]; rfl
  unfold score Benchmark.score
  rw [Score.matrixMatchScore_eq_table _ _ _ _ hρ, Score.matrixMatchScore_eq_table _ _ _ _ ht]
  congr 1
  funext x k
  change ((R.state x * singlet w (axisOfFin k)).trace).re =
    ((pull w (R.state x) * Benchmark.singlet (geometry w) k).trace).re
  rw [← representative_singlet]
  exact congrArg Complex.re ((representative_density w _ (R.positive x)
    (R.normalized x)).2.2 _).symm

theorem transport_twice {X : Type*} [Fintype X] (w : Choice) (R : Replacement X) :
    transport w (transport w R) = R := by
  cases R with
  | mk measurement state positive normalized =>
    unfold transport
    congr 1
    funext x
    exact pull_twice _ _

/-- An attaining representative strategy supplies a strategy of equal score for every
wiring in its class, by the same involution on each prepared output state. -/
theorem wiring_score {X : Type*} [Fintype X] (w : Choice) (R : Replacement X) :
    score w (transport w R) = Benchmark.score (geometry w) R := by
  rw [representative_score, transport_twice]

/-- All eight physically wired single-copy tests obey their sharp representative upper bound. -/
theorem every_wiring_ceiling {X : Type*} [Fintype X] (w : Choice) (R : Replacement X) :
    score w R ≤ if isStar w then 1 / 2 + (1 + Real.sqrt 33) / 24 else 3 / 4 := by
  rw [representative_score]
  unfold geometry
  split
  · exact (operational_ceilings _).1
  · exact (operational_ceilings _).2

#print axioms representative_score
#print axioms wiring_score
#print axioms every_wiring_ceiling
end FourSpin.Relabel
