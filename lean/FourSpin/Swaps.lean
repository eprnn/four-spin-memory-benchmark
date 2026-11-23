import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-! Finite-coordinate polynomial certificates for the four-spin pairing benchmark.
A wavefunction has one arbitrary complex amplitude for each four-bit basis ket.
A transposition acts on amplitudes by swapping the two indicated bit arguments.
The two free coefficients a and b may even be complex. -/
namespace FourSpin.Swaps

abbrev Wave := Bool → Bool → Bool → Bool → ℂ

def star (a b : ℂ) (x : Wave) : Wave := fun i j k l =>
  -a * x j i k l - b * x k j i l + (a + b) * x l j k i

def triangle (a b : ℂ) (x : Wave) : Wave := fun i j k l =>
  -a * x j i k l - b * x k j i l + (a + b) * x i k j l

def q (a b : ℂ) := 3 * (a^2 + a*b + b^2)
def r (a b : ℂ) := -4 * a * b * (a+b)

def quadratic (G : Wave → Wave) (s : ℂ) (x : Wave) : Wave :=
  fun i j k l => G (G x) i j k l - s * x i j k l

def cubic (G : Wave → Wave) (s t : ℂ) (x : Wave) : Wave :=
  fun i j k l => G (G (G x)) i j k l - s * G x i j k l - t * x i j k l

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem triangle_annihilator (a b : ℂ) (x : Wave) :
    triangle a b (quadratic (triangle a b) (q a b) x) = (fun _ _ _ _ => 0) := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp only [quadratic, triangle, q] <;> ring

/-- Read the amplitude at the lexicographically first member of each orbit of
the Klein four group of double transpositions. This finite table keeps the
kernel certificate small by separating the two degree-three factors. -/
private def orbitRepresentative (x : Wave) : Wave
  | false, false, false, false => x false false false false
  | false, false, false, true => x false false false true
  | false, false, true, false => x false false false true
  | false, false, true, true => x false false true true
  | false, true, false, false => x false false false true
  | false, true, false, true => x false true false true
  | false, true, true, false => x false true true false
  | false, true, true, true => x false true true true
  | true, false, false, false => x false false false true
  | true, false, false, true => x false true true false
  | true, false, true, false => x false true false true
  | true, false, true, true => x false true true true
  | true, true, false, false => x false false true true
  | true, true, false, true => x false true true true
  | true, true, true, false => x false true true true
  | true, true, true, true => x true true true true

private theorem cubic_fixed (a b : ℂ) (x : Wave) :
    cubic (star a b) (q a b) (r a b) x =
      orbitRepresentative (cubic (star a b) (q a b) (r a b) x) := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp only [orbitRepresentative, cubic, star, q, r] <;> ring

private theorem star_on_orbits (a b : ℂ) (x : Wave) :
    star a b (quadratic (star a b) (q a b) (orbitRepresentative x)) =
      (fun _ _ _ _ => 0) := by
  funext i j k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp only [quadratic, star, q, orbitRepresentative] <;> ring

theorem star_annihilator (a b : ℂ) (x : Wave) :
    star a b (quadratic (star a b) (q a b) (cubic (star a b) (q a b) (r a b) x))
      = (fun _ _ _ _ => 0) := by
  rw [cubic_fixed a b x]
  exact star_on_orbits a b _

#print axioms triangle_annihilator
#print axioms star_annihilator

end FourSpin.Swaps
