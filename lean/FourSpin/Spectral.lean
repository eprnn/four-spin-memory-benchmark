import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Scalar optimization of the reduced star and triangle polynomials in the pairing benchmark.
The reduction of the physical swap operators to these polynomials is a separate step. -/

namespace FourSpin.Spectral

/-- Coefficients of a unit vector projected on the three trine directions. -/
def Trine (a b c : ℝ) : Prop := a + b + c = 0 ∧ a^2 + b^2 + c^2 = 3/2

/-- The extremal coefficient follows from the two trine identities alone. -/
theorem abs_four_mul_le_one {a b c : ℝ} (h : Trine a b c) :
    |4 * a * b * c| ≤ 1 := by
  obtain ⟨hsum, hsq⟩ := h
  have habsum : (a + b)^2 = c^2 := by
    rw [show a + b = -c by linarith]
    ring
  have hab : 4 * a * b = 4 * c^2 - 3 := by nlinarith only [hsq, habsum]
  have hc : 0 ≤ 1 - c^2 := by nlinarith only [hsq, habsum, sq_nonneg (a-b)]
  have hid : 1 - ((4 * c^2 - 3) * c)^2 = (1 - c^2) * (4 * c^2 - 1)^2 := by ring
  have hbound : 0 ≤ 1 - ((4 * c^2 - 3) * c)^2 := by
    rw [hid]
    exact mul_nonneg hc (sq_nonneg _)
  rw [hab, abs_le]
  constructor
  · nlinarith only [hbound, sq_nonneg ((4 * c^2 - 3) * c + 1)]
  · nlinarith only [hbound, sq_nonneg ((4 * c^2 - 3) * c - 1)]

noncomputable def starTop : ℝ := (1 + Real.sqrt 33) / 4

private theorem root_pair (x : ℝ) :
    (x - starTop) * (x - (1 - Real.sqrt 33) / 4) = x^2 - x/2 - 2 := by
  unfold starTop
  nlinarith only [Real.sq_sqrt (show 0 ≤ (33:ℝ) by norm_num)]

private theorem cubic_factor (x : ℝ) :
    (x + 1/2) * ((x - starTop) * (x - (1 - Real.sqrt 33)/4)) =
      x^3 - 9/4*x - 1 := by
  rw [root_pair]
  ring

theorem three_halves_lt_starTop : (3/2:ℝ) < starTop := by
  have h : 5 < Real.sqrt 33 := by
    by_contra! hn
    have hp := mul_nonneg (sub_nonneg.mpr hn)
      (show (0:ℝ) ≤ 5 + Real.sqrt 33 by positivity)
    nlinarith only [hp, Real.sq_sqrt (show 0 ≤ (33:ℝ) by norm_num)]
  unfold starTop
  linarith

/-- Bound every real root of the star cubic, including directions with negative product. -/
theorem star_cubic_le {a b c x : ℝ} (h : Trine a b c)
    (hx : x^3 - 9/4*x = 4*a*b*c) : x ≤ starTop := by
  have habc := (abs_le.mp (abs_four_mul_le_one h)).2
  by_contra! hlarge
  have hpos : 0 < x + 1/2 := by linarith [three_halves_lt_starTop]
  have hother : (1 - Real.sqrt 33) / 4 ≤ starTop := by
    unfold starTop
    linarith [Real.sqrt_nonneg 33]
  have hfactor := mul_pos hpos (mul_pos (sub_pos.mpr hlarge)
    (sub_pos.mpr (lt_of_le_of_lt hother hlarge)))
  rw [cubic_factor] at hfactor
  linarith

/-- The actual extremizing direction is one trine vector, giving coefficients (1,-1/2,-1/2). -/
theorem star_witness :
    Trine 1 (-1/2) (-1/2) ∧
    starTop^3 - 9/4*starTop = 4*1*(-1/2)*(-1/2) := by
  constructor
  · norm_num [Trine]
  · have h := cubic_factor starTop
    rw [sub_self, zero_mul, mul_zero] at h
    linarith

theorem star_cubic_max : IsGreatest
    {x : ℝ | ∃ a b c : ℝ, Trine a b c ∧ x^3 - 9/4*x = 4*a*b*c} starTop := by
  constructor
  · exact ⟨1, -1/2, -1/2, star_witness⟩
  · rintro x ⟨a, b, c, h, hx⟩
    exact star_cubic_le h hx

/-- The triangle multiplicity-sector squared length from the trine Gram matrix. -/
theorem triangle_square {a b c : ℝ} (h : Trine a b c) :
    a^2 + b^2 + c^2 - a*b - a*c - b*c = (3/2:ℝ)^2 := by
  obtain ⟨hsum, hsq⟩ := h
  have hs : (a + b + c)^2 = 0 := by rw [hsum]; norm_num
  nlinarith only [hs, hsq]

/-- Both triangle sectors together give just zero and the two signed endpoints. -/
theorem triangle_roots {a b c x : ℝ} (h : Trine a b c) :
    x * (x^2 - (a^2 + b^2 + c^2 - a*b - a*c - b*c)) = 0 ↔
    x = 0 ∨ x = -(3/2) ∨ x = 3/2 := by
  rw [triangle_square h]
  have fac : x^2 - (3/2:ℝ)^2 = (x + 3/2) * (x - 3/2) := by ring
  rw [fac, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro (hz | hn | hp)
    · exact Or.inl hz
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (hz | hn | hp)
    · exact Or.inl hz
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))

theorem triangle_max : IsGreatest
    {x : ℝ | ∃ a b c : ℝ, Trine a b c ∧
      x * (x^2 - (a^2 + b^2 + c^2 - a*b - a*c - b*c)) = 0} (3/2) := by
  constructor
  · exact ⟨1, -1/2, -1/2, star_witness.1, (triangle_roots star_witness.1).2 (Or.inr (Or.inr rfl))⟩
  · rintro x ⟨a, b, c, h, hx⟩
    rcases (triangle_roots h).1 hx with rfl | rfl | rfl <;> norm_num

/-- The zero spin-two root and the spin-zero pair also obey the star bound. -/
theorem star_all_sectors_le {a b c x : ℝ} (h : Trine a b c)
    (hx : x * ((x^2 - (3/2:ℝ)^2) * (x^3 - 9/4*x - 4*a*b*c)) = 0) :
    x ≤ starTop := by
  rcases mul_eq_zero.mp hx with hz | hrest
  · linarith [three_halves_lt_starTop]
  rcases mul_eq_zero.mp hrest with hquad | hcubic
  · have hsub : x * (x^2 - (a^2+b^2+c^2-a*b-a*c-b*c)) = 0 := by
      rw [triangle_square h, hquad, mul_zero]
    rcases (triangle_roots h).1 hsub with hz | hn | hp <;>
      linarith [three_halves_lt_starTop]
  · exact star_cubic_le h (by linarith)

theorem score_constants :
    1/2 + starTop/6 = 1/2 + (1 + Real.sqrt 33)/24 ∧
    (1/2:ℝ) + (3/2)/6 = 3/4 := by
  constructor
  · unfold starTop
    ring
  · norm_num

/-- Coefficients on the two trine axes other than the first, in planar coordinates. -/
noncomputable def axisB (u v : ℝ) : ℝ := (-u + Real.sqrt 3 * v)/2
noncomputable def axisC (u v : ℝ) : ℝ := (-u - Real.sqrt 3 * v)/2

theorem planar_trine_identities (u v : ℝ) :
    u + axisB u v + axisC u v = 0 ∧
    u^2 + (axisB u v)^2 + (axisC u v)^2 = 3/2 * (u^2+v^2) := by
  unfold axisB axisC
  constructor
  · ring
  · have hs := congrArg (fun z : ℝ => z * v^2)
      (Real.sq_sqrt (show 0 ≤ (3:ℝ) by norm_num))
    dsimp at hs
    nlinarith only [hs]

/-- Every disk direction is a nonnegative contraction of a normalized trine triple.
At the origin any circle representative works; here it is the positive first axis. -/
theorem disk_decomposition (u v : ℝ) (hd : u^2 + v^2 ≤ 1) :
    ∃ r a b c : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ r^2 = u^2+v^2 ∧ Trine a b c ∧
      u = r*a ∧ axisB u v = r*b ∧ axisC u v = r*c := by
  let r := Real.sqrt (u^2+v^2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = u^2+v^2 := Real.sq_sqrt (by positivity)
  have hr1 : r ≤ 1 := by nlinarith only [hr2, hd, sq_nonneg (r-1)]
  obtain ⟨hsum, hsq⟩ := planar_trine_identities u v
  by_cases hz : r = 0
  · have hzero : u^2 + v^2 = 0 := by rw [← hr2, hz]; norm_num
    have hu2 : u^2 = 0 := by nlinarith only [hzero, sq_nonneg u, sq_nonneg v]
    have hv2 : v^2 = 0 := by linarith only [hzero, hu2]
    have hu : u=0 := by simpa using hu2
    have hv : v=0 := by simpa using hv2
    refine ⟨r, 1, -1/2, -1/2, hr, hr1, hr2, star_witness.1, ?_⟩
    simp [hu, hv, hz, axisB, axisC]
  · refine ⟨r, u/r, axisB u v/r, axisC u v/r, hr, hr1, hr2, ?_, ?_⟩
    · constructor
      · calc
          u/r + axisB u v/r + axisC u v/r = (u + axisB u v + axisC u v)/r := by ring
          _ = 0 := by rw [hsum, zero_div]
      · calc
          (u/r)^2 + (axisB u v/r)^2 + (axisC u v/r)^2 =
              (u^2 + (axisB u v)^2 + (axisC u v)^2)/r^2 := by field_simp [hz]
          _ = 3/2 := by rw [hsq, ← hr2]; field_simp [hz]
    · constructor
      · field_simp [hz]
      constructor <;> field_simp [hz]

/-- The cubic bound extends to the entire disk without assuming normalization of the input. -/
theorem star_disk_cubic_le {u v x : ℝ} (hd : u^2 + v^2 ≤ 1)
    (hx : x^3 - 9/4*(u^2+v^2)*x = 4*u*axisB u v*axisC u v) : x ≤ starTop := by
  obtain ⟨r, a, b, c, hr, hr1, hr2, ht, ha, hb, hc⟩ := disk_decomposition u v hd
  have hx' : x^3 - 9/4*r^2*x = 4*(r*a)*(r*b)*(r*c) := by
    calc
      x^3 - 9/4*r^2*x = 4*u*axisB u v*axisC u v := by rw [hr2]; exact hx
      _ = _ := by rw [hb, hc, ha]
  by_cases hz : r=0
  · have hx0 : x=0 := by simpa [hz] using hx'
    linarith only [hx0, three_halves_lt_starTop]
  · let y := x/r
    have hxy : x = r*y := by dsimp [y]; field_simp [hz]
    have hcancel : (y^3 - 9/4*y - 4*a*b*c)*r^3 = 0 := by
      calc
        _ = (r*y)^3 - 9/4*r^2*(r*y) - 4*(r*a)*(r*b)*(r*c) := by ring
        _ = 0 := by rw [← hxy]; exact sub_eq_zero.mpr hx'
    have hy := (mul_eq_zero.mp hcancel).resolve_right (pow_ne_zero _ hz)
    have hybound := star_cubic_le ht (sub_eq_zero.mp hy)
    calc
      x = r*y := hxy
      _ ≤ r*starTop := mul_le_mul_of_nonneg_left hybound hr
      _ ≤ starTop := by
        have htop : 0 ≤ starTop := by linarith only [three_halves_lt_starTop]
        nlinarith only [mul_nonneg (sub_nonneg.mpr hr1) htop]

/-- The triangle scalar criterion on a disk direction, including the zero sector. -/
theorem triangle_disk_abs_le {u v x : ℝ} (hd : u^2 + v^2 ≤ 1)
    (hx : x * (x^2 - (9/4)*(u^2+v^2)) = 0) : |x| ≤ 3/2 := by
  rcases mul_eq_zero.mp hx with hzero | hquad
  · rw [hzero, abs_zero]; norm_num
  · rw [abs_le]
    constructor
    · nlinarith only [hd, hquad, sq_nonneg (x+3/2)]
    · nlinarith only [hd, hquad, sq_nonneg (x-3/2)]

#print axioms disk_decomposition
#print axioms star_disk_cubic_le
#print axioms triangle_disk_abs_le

#print axioms star_all_sectors_le
#print axioms score_constants
#print axioms abs_four_mul_le_one
#print axioms star_cubic_max
#print axioms three_halves_lt_starTop
#print axioms triangle_max
#print axioms triangle_roots

end FourSpin.Spectral
