import FourSpin.Ceilings
import FourSpin.Expectation

open Matrix
open scoped ComplexOrder

namespace FourSpin.PhysicalMatrix

open Swaps Ceilings Spectral

/-- The computational basis of the four physical two-level sites. -/
abbrev Index := Bool × Bool × Bool × Bool

theorem index_card : Fintype.card Index = 16 := by decide

def swap12 : Index → Index := fun (i, j, k, l) => (j, i, k, l)
def swap13 : Index → Index := fun (i, j, k, l) => (k, j, i, l)
def swap14 : Index → Index := fun (i, j, k, l) => (l, j, k, i)
def swap23 : Index → Index := fun (i, j, k, l) => (i, k, j, l)

theorem swap12_involutive : Function.Involutive swap12 := by
  rintro ⟨i, j, k, l⟩
  rfl

theorem swap13_involutive : Function.Involutive swap13 := by
  rintro ⟨i, j, k, l⟩
  rfl

theorem swap14_involutive : Function.Involutive swap14 := by
  rintro ⟨i, j, k, l⟩
  rfl

theorem swap23_involutive : Function.Involutive swap23 := by
  rintro ⟨i, j, k, l⟩
  rfl

/-- For an involution, the matrix both sends a ket at `j` to the ket at
`f j` and pulls amplitudes back along `f`. -/
noncomputable def swapMatrix (f : Index → Index) : Matrix Index Index ℂ :=
  Matrix.of fun i j => if f i = j then 1 else 0

theorem swapMatrix_hermitian (f : Index → Index) (hf : Function.Involutive f) :
    (swapMatrix f).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h : f j = i ↔ f i = j := by
    constructor
    · intro hi
      rw [← hi, hf]
    · intro hj
      rw [← hj, hf]
  by_cases hij : f i = j
  · simp [swapMatrix, hij, h.mpr hij]
  · have hji : f j ≠ i := fun hji => hij (h.mp hji)
    simp [swapMatrix, hij, hji]

theorem swapMatrix_mulVec (f : Index → Index) (v : Index → ℂ) (i : Index) :
    (swapMatrix f *ᵥ v) i = v (f i) := by
  simp [swapMatrix, Matrix.mulVec, dotProduct, ite_mul]

/-- Signed physical swap sum for a trine direction. The explicit minus signs
are the conversion from swaps to the observables `2 Q - I`. -/
noncomputable def signedSwapSum (f₁ f₂ f₃ : Index → Index) (a b c : ℝ) :
    Matrix Index Index ℂ :=
  (-a) • swapMatrix f₁ + (-b) • swapMatrix f₂ + (-c) • swapMatrix f₃

theorem signedSwapSum_hermitian {f₁ f₂ f₃ : Index → Index}
    (h₁ : Function.Involutive f₁) (h₂ : Function.Involutive f₂)
    (h₃ : Function.Involutive f₃) (a b c : ℝ) :
    (signedSwapSum f₁ f₂ f₃ a b c).IsHermitian := by
  unfold signedSwapSum Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    star_trivial, (swapMatrix_hermitian f₁ h₁).eq, (swapMatrix_hermitian f₂ h₂).eq,
    (swapMatrix_hermitian f₃ h₃).eq]

theorem signedSwapSum_mulVec (f₁ f₂ f₃ : Index → Index) (a b c : ℝ)
    (v : Index → ℂ) (i : Index) :
    (signedSwapSum f₁ f₂ f₃ a b c *ᵥ v) i =
      (-a : ℝ) • v (f₁ i) + (-b : ℝ) • v (f₂ i) + (-c : ℝ) • v (f₃ i) := by
  simp only [signedSwapSum, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    Pi.smul_apply, swapMatrix_mulVec]

/-- Star wiring 12, 13, 14 with trine coefficients `a, b, -(a+b)`. -/
noncomputable def starMatrix (a b : ℝ) : Matrix Index Index ℂ :=
  signedSwapSum swap12 swap13 swap14 a b (-(a + b))

/-- Triangle wiring 12, 13, 23 with the same convention. -/
noncomputable def triangleMatrix (a b : ℝ) : Matrix Index Index ℂ :=
  signedSwapSum swap12 swap13 swap23 a b (-(a + b))

theorem starMatrix_hermitian (a b : ℝ) : (starMatrix a b).IsHermitian :=
  signedSwapSum_hermitian swap12_involutive swap13_involutive swap14_involutive a b _

theorem triangleMatrix_hermitian (a b : ℝ) : (triangleMatrix a b).IsHermitian :=
  signedSwapSum_hermitian swap12_involutive swap13_involutive swap23_involutive a b _

def toWave (v : Index → ℂ) : Wave := fun i j k l => v (i, j, k, l)

theorem toWave_ne_zero {v : Index → ℂ} (hv : v ≠ 0) : toWave v ≠ zeroWave := by
  intro h
  apply hv
  funext i
  obtain ⟨i, j, k, l⟩ := i
  exact congrArg (fun w : Wave => w i j k l) h

theorem toWave_real_smul (x : ℝ) (v : Index → ℂ) :
    toWave (x • v) = scale (x : ℂ) (toWave v) := by
  funext i j k l
  simp only [toWave, scale, Pi.smul_apply, Complex.real_smul]

theorem toWave_starMatrix_mulVec (a b : ℝ) (v : Index → ℂ) :
    toWave (starMatrix a b *ᵥ v) = Swaps.star a b (toWave v) := by
  funext i j k l
  simp only [toWave, starMatrix, signedSwapSum_mulVec, swap12, swap13, swap14,
    Swaps.star, neg_neg, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_add,
    neg_mul, sub_eq_add_neg]

theorem toWave_triangleMatrix_mulVec (a b : ℝ) (v : Index → ℂ) :
    toWave (triangleMatrix a b *ᵥ v) = Swaps.triangle a b (toWave v) := by
  funext i j k l
  simp only [toWave, triangleMatrix, signedSwapSum_mulVec, swap12, swap13, swap23,
    Swaps.triangle, neg_neg, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_add,
    neg_mul, sub_eq_add_neg]

/-- Use the three trine coefficients directly in the physical signed sum. -/
theorem starMatrix_eq_signedSwapSum {a b c : ℝ} (h : Trine a b c) :
    starMatrix a b = signedSwapSum swap12 swap13 swap14 a b c := by
  have hc : c = -(a + b) := by linarith [h.1]
  rw [hc, starMatrix]

theorem triangleMatrix_eq_signedSwapSum {a b c : ℝ} (h : Trine a b c) :
    triangleMatrix a b = signedSwapSum swap12 swap13 swap23 a b c := by
  have hc : c = -(a + b) := by linarith [h.1]
  rw [hc, triangleMatrix]

/-- The spectral bound controls the expectation for an arbitrary normalized,
positive semidefinite four-spin state, including states outside the code. -/
theorem star_expectation_le {a b c : ℝ} (h : Trine a b c) {ρ : Matrix Index Index ℂ}
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (ρ * starMatrix a b).trace.re ≤ starTop := by
  apply expectation_le_of_eigenpair_bound hρ htrace (starMatrix_hermitian a b)
  intro x v hv heig
  apply star_eigen_le h (toWave_ne_zero hv)
  have hw := congrArg toWave heig
  rwa [toWave_starMatrix_mulVec, toWave_real_smul] at hw

/-- The analogous full-space bound for the representative triangle. -/
theorem triangle_expectation_le {a b c : ℝ} (h : Trine a b c) {ρ : Matrix Index Index ℂ}
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (ρ * triangleMatrix a b).trace.re ≤ 3 / 2 := by
  apply expectation_le_of_eigenpair_bound hρ htrace (triangleMatrix_hermitian a b)
  intro x v hv heig
  apply triangle_eigen_le h (toWave_ne_zero hv)
  have hw := congrArg toWave heig
  rwa [toWave_triangleMatrix_mulVec, toWave_real_smul] at hw

#print axioms swapMatrix_hermitian
#print axioms swapMatrix_mulVec
#print axioms star_expectation_le
#print axioms triangle_expectation_le

end FourSpin.PhysicalMatrix
