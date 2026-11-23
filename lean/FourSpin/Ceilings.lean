import FourSpin.Swaps
import FourSpin.Spectral

namespace FourSpin.Ceilings
open Swaps Spectral

def scale (z : ℂ) (v : Wave) : Wave := fun i j k l => z * v i j k l
def zeroWave : Wave := fun _ _ _ _ => 0

private theorem scale_scale (a b : ℂ) (v : Wave) :
    scale a (scale b v) = scale (a*b) v := by
  funext i j k l
  simp [scale, mul_assoc]

private theorem star_scale (a b z : ℂ) (v : Wave) :
    star a b (scale z v) = scale z (star a b v) := by
  funext i j k l
  simp only [Swaps.star, scale]
  ring

private theorem triangle_scale (a b z : ℂ) (v : Wave) :
    triangle a b (scale z v) = scale z (triangle a b v) := by
  funext i j k l
  simp only [triangle, scale]
  ring

private theorem scale_zero {v : Wave} (hv : v ≠ zeroWave) {z : ℂ}
    (h : scale z v = zeroWave) : z = 0 := by
  by_contra hz
  apply hv
  funext i j k l
  have h₀ := congrArg (fun w : Wave => w i j k l) h
  change z * v i j k l = 0 at h₀
  exact (mul_eq_zero.mp h₀).resolve_left hz

private theorem quadratic_eigen {G : Wave → Wave} {v : Wave} {x : ℂ}
    (lin : ∀ z w, G (scale z w) = scale z (G w))
    (eig : G v = scale x v) (s : ℂ) :
    quadratic G s v = scale (x^2-s) v := by
  have he : G (G v) = scale (x*x) v := by
    conv_lhs => arg 1; rw [eig]
    rw [lin, eig, scale_scale]
  funext i j k l
  simp only [quadratic, he, scale]
  ring

private theorem cubic_eigen {G : Wave → Wave} {v : Wave} {x : ℂ}
    (lin : ∀ z w, G (scale z w) = scale z (G w))
    (eig : G v = scale x v) (s t : ℂ) :
    cubic G s t v = scale (x^3-s*x-t) v := by
  have he : G (G v) = scale (x*x) v := by
    conv_lhs => arg 1; rw [eig]
    rw [lin, eig, scale_scale]
  have he' : G (G (G v)) = scale ((x*x)*x) v := by
    rw [he, lin, eig, scale_scale]
  funext i j k l
  unfold cubic
  rw [he', eig]
  simp only [scale]
  ring

private theorem quadratic_scale {G : Wave → Wave}
    (lin : ∀ z w, G (scale z w) = scale z (G w)) (s z : ℂ) (v : Wave) :
    quadratic G s (scale z v) = scale z (quadratic G s v) := by
  funext i j k l
  simp only [quadratic, lin, scale]
  ring

private theorem coefficients {a b c : ℝ} (h : Trine a b c) :
    q (a:ℂ) (b:ℂ) = 9/4 ∧ r (a:ℂ) (b:ℂ) = ((4*a*b*c:ℝ):ℂ) := by
  obtain ⟨hs, hn⟩ := h
  have hc : c = -(a+b) := by linarith
  subst c
  constructor
  · have hq : 3*(a^2+a*b+b^2) = 9/4 := by nlinarith only [hn]
    unfold q
    simpa [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add] using congrArg Complex.ofReal hq
  · simp only [r, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_add,
      Complex.ofReal_ofNat]
    ring

/-- Any real eigenvalue on any nonzero complex four-spin wave, for a unit
trine direction, obeys the star bound. -/
theorem star_eigen_le {a b c x : ℝ} (h : Trine a b c) {v : Wave}
    (hv : v ≠ zeroWave) (eig : star a b v = scale x v) : x ≤ starTop := by
  obtain ⟨hq, hr⟩ := coefficients h
  have hn := star_annihilator (a:ℂ) (b:ℂ) v
  rw [cubic_eigen (star_scale (a:ℂ) (b:ℂ)) eig, quadratic_scale (star_scale (a:ℂ) (b:ℂ)),
      quadratic_eigen (star_scale (a:ℂ) (b:ℂ)) eig, scale_scale, star_scale, eig, scale_scale] at hn
  have root := scale_zero hv hn
  rw [hq, hr] at root
  have realRoot : (x^3 - 9/4*x - 4*a*b*c) * (x^2-9/4) * x = 0 := by
    apply Complex.ofReal_injective
    push_cast
    push_cast at root
    exact root
  rcases mul_eq_zero.mp realRoot with hf | hz
  · rcases mul_eq_zero.mp hf with hc | hq'
    · exact star_cubic_le h (by linarith)
    · have hx : x ≤ (3/2:ℝ) := by nlinarith [sq_nonneg (x-3/2)]
      exact le_trans hx three_halves_lt_starTop.le
  · rw [hz]
    linarith [three_halves_lt_starTop]

/-- The corresponding bound for a triangle, on the same full complex space. -/
theorem triangle_eigen_le {a b c x : ℝ} (h : Trine a b c) {v : Wave}
    (hv : v ≠ zeroWave) (eig : triangle a b v = scale x v) : x ≤ 3/2 := by
  obtain ⟨hq, _⟩ := coefficients h
  have hn := triangle_annihilator (a:ℂ) (b:ℂ) v
  rw [quadratic_eigen (triangle_scale (a:ℂ) (b:ℂ)) eig, triangle_scale, eig, scale_scale] at hn
  have root := scale_zero hv hn
  rw [hq] at root
  have realRoot : (x^2-9/4)*x = 0 := by
    apply Complex.ofReal_injective
    push_cast
    exact root
  rcases mul_eq_zero.mp realRoot with hs | hz
  · nlinarith [sq_nonneg (x-3/2)]
  · rw [hz]; norm_num

#print axioms star_eigen_le
#print axioms triangle_eigen_le
end FourSpin.Ceilings
