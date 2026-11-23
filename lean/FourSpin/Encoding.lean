import FourSpin.Benchmark
import Mathlib.Tactic.FinCases

/-! Explicit two-column encoding in the ordered computational basis of four spins. -/
namespace FourSpin.Encoding
open PhysicalMatrix Benchmark
open scoped BigOperators
noncomputable section

/-- Coefficients of the unnormalized antisymmetric two-spin ket |01⟩−|10⟩. -/
def eps (i j : Bool) : ℤ := if i = j then 0 else if i then -1 else 1

/-- Product of the unnormalized singlets on pairs 12 and 34. -/
def p : Index → ℤ := fun (i,j,k,l) => eps i j * eps k l

/-- Twice the coefficients of the orthogonal triplet-pair singlet before normalization. -/
def q : Index → ℤ := fun (i,j,k,l) =>
  if i = j then (if k = l ∧ i ≠ k then 2 else 0) else (if k ≠ l then -1 else 0)

/-- The columns are p/2 and √3 q/6. The sign of the second column fixes the X convention. -/
def V : Matrix Index (Fin 2) ℂ :=
  fun i a => if a = 0 then ((p i : ℝ)/2 : ℝ) else (Real.sqrt 3 * (q i : ℝ)/6 : ℝ)

def swap24 : Index → Index := fun (i,j,k,l) => (i,l,k,j)
def swap34 : Index → Index := fun (i,j,k,l) => (i,j,l,k)
def edge (a : Fin 3) (other : Bool) : Index → Index :=
  if other then ![swap34, swap24, swap23] a else ![swap12, swap13, swap14] a

private theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ)^2 = 3 := by
  exact_mod_cast Real.sq_sqrt (show 0 ≤ (3:ℝ) by norm_num)

/-- Normalization and orthogonality are evaluated over all sixteen basis rows. -/
theorem isometry : V.conjTranspose * V = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      V, p, q, eps, Complex.star_def, Fintype.sum_prod_type, Fintype.sum_bool]
  ring_nf
  norm_num [sqrt3_sq]

private theorem swap_on_V (f : Index → Index) (i : Index) (k : Fin 2) :
    ((-swapMatrix f) * V) i k = -V (f i) k := by
  simp [Matrix.mul_apply, swapMatrix, ite_mul]

/-- The integer coefficient relations for all six signed transpositions. -/
private theorem coords0 : ∀ (b : Bool) (i : Index),
    p (edge 0 b i) = -p i ∧ q (edge 0 b i) = q i := by decide
private theorem coords1 : ∀ (b : Bool) (i : Index),
    2 * p (edge 1 b i) = p i - q i ∧ 2 * q (edge 1 b i) = -3*p i - q i := by decide
private theorem coords2 : ∀ (b : Bool) (i : Index),
    2 * p (edge 2 b i) = p i + q i ∧ 2 * q (edge 2 b i) = 3*p i - q i := by decide

/-- Each signed swap leaves the code invariant and acts there by exactly the benchmark axis. -/
theorem intertwine (a : Fin 3) (b : Bool) :
    (-swapMatrix (edge a b)) * V = V * setting a := by
  ext i k
  rw [swap_on_V]
  fin_cases a
  · obtain ⟨hp, hq⟩ := coords0 b i
    fin_cases k <;> norm_num [V, setting, Input.axis, Matrix.mul_apply, Fin.sum_univ_two, hp, hq]
    ring
  · obtain ⟨hp, hq⟩ := coords1 b i
    have hp' : 2 * (p (edge 1 b i) : ℂ) = (p i : ℂ) - q i := by exact_mod_cast hp
    have hq' : 2 * (q (edge 1 b i) : ℂ) = -3*(p i : ℂ) - q i := by exact_mod_cast hq
    fin_cases k <;> norm_num [V, setting, Input.axis, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -hp'/4 - (q i : ℂ) * sqrt3_sq/12
    · linear_combination -(Real.sqrt 3 : ℂ)*hq'/12
  · change -V (edge 2 b i) k = (V * setting 2) i k
    obtain ⟨hp, hq⟩ := coords2 b i
    have hp' : 2 * (p (edge 2 b i) : ℂ) = (p i : ℂ) + q i := by exact_mod_cast hp
    have hq' : 2 * (q (edge 2 b i) : ℂ) = 3*(p i : ℂ) - q i := by exact_mod_cast hq
    fin_cases k <;> norm_num [V, setting, Input.axis, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_two]
    · linear_combination -hp'/4 + (q i : ℂ) * sqrt3_sq/12
    · linear_combination -(Real.sqrt 3 : ℂ)*hq'/12

theorem compressed_observables (a : Fin 3) (b : Bool) :
    V.conjTranspose * (-swapMatrix (edge a b)) * V = setting a := by
  rw [Matrix.mul_assoc, intertwine, ← Matrix.mul_assoc, isometry, Matrix.one_mul]

/-- For four spin halves, total spin squared in swap coordinates is the sum of the six swaps. -/
def totalSpinSquared : Matrix Index Index ℂ :=
  ∑ a, (swapMatrix (edge a false) + swapMatrix (edge a true))

private theorem sum_axes : setting 0 + setting 1 + setting 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [setting, Input.axis, Matrix.cons_val_two]

theorem totalSpinSquared_code : totalSpinSquared * V = 0 := by
  have act (a : Fin 3) (b : Bool) : swapMatrix (edge a b) * V = -(V * setting a) := by
    have h := intertwine a b
    rwa [Matrix.neg_mul, neg_eq_iff_eq_neg] at h
  have hsum : V * setting 0 + V * setting 1 + V * setting 2 = 0 := by
    rw [← Matrix.mul_add, ← Matrix.mul_add, sum_axes, Matrix.mul_zero]
  simp only [totalSpinSquared, Fin.sum_univ_three, Matrix.add_mul, act]
  calc
    _ = -((V*setting 0 + V*setting 1 + V*setting 2) +
          (V*setting 0 + V*setting 1 + V*setting 2)) := by abel
    _ = 0 := by rw [hsum]; simp

/-- With false denoting spin up, b=false is the collective raising operator and
b=true the collective lowering operator. Each term pulls the amplitude of
a ket differing at one site, when that spin flip has the specified output. -/
def ladder (b : Bool) (ψ : Index → ℂ) : Index → ℂ := fun (i,j,k,l) =>
  (if i = b then ψ (!i,j,k,l) else 0) + (if j = b then ψ (i,!j,k,l) else 0) +
  (if k = b then ψ (i,j,!k,l) else 0) + (if l = b then ψ (i,j,k,!l) else 0)

def zSpin (b : Bool) : ℂ := if b then -1/2 else 1/2

/-- The physical collective Jz operator with local eigenvalues ±1/2. -/
def totalZ (ψ : Index → ℂ) : Index → ℂ := fun (i,j,k,l) =>
  (zSpin i + zSpin j + zSpin k + zSpin l) * ψ (i,j,k,l)

/-- Direct singlet check independent of the swap expression for J². -/
theorem generators_annihilate (a : Fin 2) :
    (∀ b : Bool, ladder b (fun i => V i a) = 0) ∧ totalZ (fun i => V i a) = 0 := by
  constructor
  · intro b
    funext i
    rcases i with ⟨i,j,k,l⟩
    cases b <;> cases i <;> cases j <;> cases k <;> cases l <;> fin_cases a <;>
      norm_num [ladder, V, p, q, eps] <;> ring
  · funext i
    rcases i with ⟨i,j,k,l⟩
    cases i <;> cases j <;> cases k <;> cases l <;> fin_cases a <;>
      norm_num [totalZ, zSpin, V, p, q, eps]

#print axioms generators_annihilate
#print axioms isometry
#print axioms intertwine
#print axioms compressed_observables
#print axioms totalSpinSquared_code

end
end FourSpin.Encoding
