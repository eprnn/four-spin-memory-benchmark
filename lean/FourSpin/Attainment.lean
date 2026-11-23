import FourSpin.Benchmark
import FourSpin.TrineMeasurement
import FourSpin.Witness
import Mathlib.Tactic.FinCases
import FourSpin.Score
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The explicit trine measurement and physical output states form a finite
measure-and-prepare strategy for the representative star and triangle.
This file proves attainment of the six-trial Born score in Benchmark. -/

open Matrix BigOperators
open scoped ComplexOrder

namespace FourSpin.Attainment

noncomputable section

variable {n : Type*} [Fintype n]

/-- The squared norm of the ket in the computational basis. -/
def ketNormSq (v : n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- Rank-one density operator obtained by normalizing a ket. -/
def pure (v : n → ℂ) : Matrix n n ℂ :=
  (ketNormSq v)⁻¹ • vecMulVec v (star v)

theorem ketNormSq_pos {v : n → ℂ} (hv : v ≠ 0) : 0 < ketNormSq v := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! hn
    exact hv (funext hn)
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (v j))
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

theorem pure_psd (v : n → ℂ) : (pure v).PosSemidef := by
  apply (Matrix.posSemidef_vecMulVec_self_star v).smul
  exact inv_nonneg.mpr (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i))

theorem pure_trace {v : n → ℂ} (hv : v ≠ 0) : (pure v).trace = 1 := by
  have hn := ne_of_gt (ketNormSq_pos hv)
  have hnorm : (vecMulVec v (star v)).trace = (ketNormSq v : ℂ) := by
    rw [Matrix.trace_vecMulVec]
    simp [dotProduct, Complex.mul_conj, ketNormSq]
  rw [pure, Matrix.trace_smul, hnorm, Complex.real_smul, ← Complex.ofReal_mul]
  simp [hn]

theorem pure_born_eigen {v : n → ℂ} (hv : v ≠ 0) (A : Matrix n n ℂ) (e : ℝ)
    (he : A *ᵥ v = e • v) : Score.born (pure v) A = e := by
  have hm : A * pure v = e • pure v := by
    simp only [pure, Matrix.mul_smul, Matrix.mul_vecMulVec, he, Matrix.smul_vecMulVec,
      smul_comm ((ketNormSq v)⁻¹) e]
  unfold Score.born
  rw [Matrix.trace_mul_comm, hm, Matrix.trace_smul, pure_trace hv]
  simp

open PhysicalMatrix Benchmark

/-- Send a real-valued witness to the physical complex computational basis. -/
def complexKet (w : Witness.Wave) : Index → ℂ :=
  fun (i, j, k, l) => w i j k l

theorem complexKet_ne_zero {w : Witness.Wave} (hw : w ≠ 0) : complexKet w ≠ 0 := by
  intro h
  apply hw
  funext i j k l
  have hh := congrArg (fun v : Index → ℂ => (v (i, j, k, l)).re) h
  simpa [complexKet] using hh

def branchWave : Geometry → Fin 3 → Witness.Wave
  | .star => ![Witness.starBranch1, Witness.starBranch2, Witness.starBranch3]
  | .triangle => ![Witness.triangleBranch, Witness.triangleBranch2, Witness.triangleBranch3]

theorem branchWave_ne_zero (g : Geometry) (x : Fin 3) : branchWave g x ≠ 0 := by
  cases g <;> fin_cases x
  · exact Witness.starBranch1_nonzero
  · exact Witness.starBranch2_nonzero
  · exact Witness.starBranch3_nonzero
  · exact Witness.triangleBranch_nonzero
  · exact Witness.triangleBranch2_nonzero
  · exact Witness.triangleBranch3_nonzero

def branchKet (g : Geometry) (x : Fin 3) : Index → ℂ := complexKet (branchWave g x)

def branchState (g : Geometry) (x : Fin 3) : Matrix Index Index ℂ := pure (branchKet g x)

theorem branchState_positive (g : Geometry) (x : Fin 3) : (branchState g x).PosSemidef :=
  pure_psd _

theorem branchState_normalized (g : Geometry) (x : Fin 3) : (branchState g x).trace = 1 :=
  pure_trace (complexKet_ne_zero (branchWave_ne_zero g x))

def branchOperator (g : Geometry) (x : Fin 3) : Matrix Index Index ℂ :=
  ∑ a, Score.trineOverlap x a • ((2 : ℝ) • singlet g a - 1)

private theorem branchOperator_eq (g : Geometry) (x : Fin 3) :
    branchOperator g x =
      signedSwapSum (g.pair 0) (g.pair 1) (g.pair 2)
        (Score.trineOverlap x 0) (Score.trineOverlap x 1) (Score.trineOverlap x 2) := by
  simp only [branchOperator, signed_singlet, Fin.sum_univ_three, signedSwapSum, neg_smul, smul_neg]

private theorem signedSwapSum_complexKet (g : Geometry) (a b c : ℝ) (w : Witness.Wave) :
    signedSwapSum (g.pair 0) (g.pair 1) (g.pair 2) a b c *ᵥ complexKet w =
      complexKet ((match g with | .star => Witness.star | .triangle => Witness.triangle) a b c w) := by
  funext i
  obtain ⟨i, j, k, l⟩ := i
  cases g <;>
    simp [signedSwapSum_mulVec, Geometry.pair, swap12, swap13, swap14, swap23,
      complexKet, Witness.star, Witness.triangle, Complex.real_smul, sub_eq_add_neg, neg_mul]

private theorem branchWave_eigen (g : Geometry) (x : Fin 3) :
    (match g with | .star => Witness.star | .triangle => Witness.triangle)
      (Score.trineOverlap x 0) (Score.trineOverlap x 1) (Score.trineOverlap x 2) (branchWave g x) =
      fun i j k l => g.top * branchWave g x i j k l := by
  cases g <;> fin_cases x <;>
    norm_num [Score.trineOverlap, branchWave, Geometry.top, Spectral.starTop,
      Witness.starValue] <;>
    first
    | simpa [neg_div, Witness.starValue] using Witness.starBranch1_eigen
    | simpa [neg_div, Witness.starValue] using Witness.starBranch2_eigen
    | simpa [neg_div, Witness.starValue] using Witness.starBranch3_eigen
    | simpa [neg_div] using Witness.triangleBranch_eigen
    | simpa [neg_div] using Witness.triangleBranch2_eigen
    | simpa [neg_div] using Witness.triangleBranch3_eigen

theorem branchKet_eigen (g : Geometry) (x : Fin 3) :
    branchOperator g x *ᵥ branchKet g x = g.top • branchKet g x := by
  rw [branchKet, branchOperator_eq, signedSwapSum_complexKet, branchWave_eigen]
  funext i
  obtain ⟨i, j, k, l⟩ := i
  simp [complexKet, Complex.real_smul]

theorem branchState_born (g : Geometry) (x : Fin 3) :
    Score.born (branchState g x) (branchOperator g x) = g.top :=
  pure_born_eigen (complexKet_ne_zero (branchWave_ne_zero g x)) _ _ (branchKet_eigen g x)

/-- Score attainment with the two Born columns supplied by the input POVM. -/
theorem matrixScore_eq_ceiling (g : Geometry)
    (E L : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hp : ∀ x a, Score.born (E x) ((1 / 2 : ℝ) • (1 + L a)) =
      (1 / 3 : ℝ) * (1 + Score.trineOverlap x a))
    (hm : ∀ x a, Score.born (E x) ((1 / 2 : ℝ) • (1 - L a)) =
      (1 / 3 : ℝ) * (1 - Score.trineOverlap x a)) :
    Score.matrixMatchScore E (branchState g) L (singlet g) = g.ceiling := by
  have ht (x : Fin 3) : (branchState g x).trace.re = 1 := by
    rw [branchState_normalized]; simp
  rw [Score.matrixMatchScore_eq_weighted_trace _ _ _ _ (fun _ => 1 / 3) _ hp hm ht]
  change (∑ x : Fin 3, (1 / 3 : ℝ) * (1 / 2 + Score.born (branchState g x)
    (branchOperator g x) / 6)) = g.ceiling
  simp only [branchState_born, Fin.sum_univ_three, Geometry.ceiling]
  ring

/-- The same three-input-effect measurement works for both wiring geometries. -/
def trineMeasurement : POVM (Fin 3) where
  effect := TrineMeasurement.effect
  positive := TrineMeasurement.effect_psd
  complete := TrineMeasurement.povm_complete

def attainingReplacement (g : Geometry) : Replacement (Fin 3) where
  measurement := trineMeasurement
  state := branchState g
  positive := branchState_positive g
  normalized := branchState_normalized g

private theorem setting_eq_logical : setting = TrineMeasurement.logical := by
  funext a
  fin_cases a <;> rfl

theorem attainingReplacement_score (g : Geometry) :
    score g (attainingReplacement g) = g.ceiling := by
  unfold score attainingReplacement trineMeasurement
  rw [setting_eq_logical]
  exact matrixScore_eq_ceiling g TrineMeasurement.effect TrineMeasurement.logical
    TrineMeasurement.born_plus TrineMeasurement.born_minus

theorem attain_star :
    score .star (attainingReplacement .star) = 1 / 2 + (1 + Real.sqrt 33) / 24 := by
  rw [attainingReplacement_score]
  unfold Geometry.ceiling Geometry.top Spectral.starTop
  ring

theorem attain_triangle : score .triangle (attainingReplacement .triangle) = 3 / 4 := by
  rw [attainingReplacement_score]
  norm_num [Geometry.ceiling, Geometry.top]

/-- No finite-outcome measure-and-prepare strategy scores above the explicit
three-outcome strategy for either representative wiring. -/
theorem attainingReplacement_optimal {X : Type*} [Fintype X] (g : Geometry)
    (R : Replacement X) : score g R ≤ score g (attainingReplacement g) := by
  obtain ⟨hs, ht⟩ := operational_ceilings R
  cases g
  · exact hs.trans_eq attain_star.symm
  · exact ht.trans_eq attain_triangle.symm

#print axioms pure_psd
#print axioms pure_trace
#print axioms pure_born_eigen
#print axioms branchKet_eigen
#print axioms branchState_positive
#print axioms branchState_normalized
#print axioms matrixScore_eq_ceiling
#print axioms attain_star
#print axioms attain_triangle
#print axioms attainingReplacement_optimal

end
end FourSpin.Attainment
