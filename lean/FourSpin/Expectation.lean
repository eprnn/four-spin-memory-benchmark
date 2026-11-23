import Mathlib.Analysis.Matrix.Order

open scoped ComplexOrder MatrixOrder
open Matrix

namespace FourSpin

variable {ι : Type*} [Fintype ι]

/-- The trace pairing of two positive semidefinite complex matrices is real and nonnegative. -/
theorem trace_mul_nonneg_of_psd {ρ G : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hG : G.PosSemidef) : 0 ≤ (ρ * G).trace := by
  classical
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  change 0 ≤ (Bᴴ * B * G).trace
  rw [← Matrix.trace_mul_cycle B G Bᴴ]
  exact (hG.mul_mul_conjTranspose_same B).trace_nonneg

variable [DecidableEq ι]

/-- A Loewner upper certificate bounds every trace-one mixed-state expectation.
The complex order also certifies that the expectation has zero imaginary part. -/
theorem trace_expectation_le_of_psd_gap {ρ H : Matrix ι ι ℂ} {L : ℝ}
    (hρ : ρ.PosSemidef) (hnorm : ρ.trace = 1)
    (hgap : ((L : ℂ) • (1 : Matrix ι ι ℂ) - H).PosSemidef) :
    (ρ * H).trace ≤ (L : ℂ) := by
  have h := trace_mul_nonneg_of_psd hρ hgap
  simpa only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, hnorm, smul_eq_mul, mul_one, sub_nonneg] using h

/-- Convert an upper bound on each eigenvalue into a Loewner certificate. -/
theorem psd_gap_of_eigenvalues_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {L : ℝ}
    (heig : ∀ i, hH.eigenvalues i ≤ L) :
    ((L : ℂ) • (1 : Matrix ι ι ℂ) - H).PosSemidef := by
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  have hunit : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hspec : H = U * D * Uᴴ := hH.spectral_theorem
  have hdiag : ((L : ℂ) • (1 : Matrix ι ι ℂ) - D).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal]
    change (diagonal (fun _ : ι => (L : ℂ)) - diagonal
      (RCLike.ofReal ∘ hH.eigenvalues)).PosSemidef
    rw [Matrix.diagonal_sub]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change 0 ≤ (L : ℂ) - (hH.eigenvalues i : ℂ)
    exact sub_nonneg.mpr (Complex.real_le_real.mpr (heig i))
  have h := hdiag.mul_mul_conjTranspose_same U
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hunit, ← hspec] using h

/-- Spectral upper bounds apply to the real expectation of every density matrix on
the same finite space, including arbitrary correlated four-spin outputs. -/
theorem expectation_le_of_eigenvalues_le {ρ H : Matrix ι ι ℂ} {L : ℝ}
    (hρ : ρ.PosSemidef) (hnorm : ρ.trace = 1) (hH : H.IsHermitian)
    (heig : ∀ i, hH.eigenvalues i ≤ L) : (ρ * H).trace.re ≤ L := by
  exact (Complex.le_def.mp
    (trace_expectation_le_of_psd_gap hρ hnorm (psd_gap_of_eigenvalues_le hH heig))).1

/-- Equivalent entry point for a bound proved by applying a polynomial identity
to arbitrary nonzero eigenvectors in the computational basis. -/
theorem expectation_le_of_eigenpair_bound {ρ H : Matrix ι ι ℂ} {L : ℝ}
    (hρ : ρ.PosSemidef) (hnorm : ρ.trace = 1) (hH : H.IsHermitian)
    (heig : ∀ (t : ℝ) (v : ι → ℂ), v ≠ 0 → H *ᵥ v = t • v → t ≤ L) :
    (ρ * H).trace.re ≤ L :=
  expectation_le_of_eigenvalues_le hρ hnorm hH fun i =>
    heig _ _ (hH.eigenvectorBasis.orthonormal.ne_zero i) (hH.mulVec_eigenvectorBasis i)

end FourSpin
