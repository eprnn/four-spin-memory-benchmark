import FourSpin.Relabel
import FourSpin.Attainment

namespace FourSpin

/-- Scores attainable by measuring a single input and preparing a four-spin
output. Every strategy has a finite outcome type of arbitrary cardinality. -/
def attainableScores (w : Wiring.Choice) : Set ℝ :=
  {s | ∃ (n : ℕ) (R : Benchmark.Replacement (Fin n)), Relabel.score w R = s}

/-- The paper's star–triangle dichotomy for the ideal six-trial benchmark.
The result is a maximum, so both its upper bound and its attainment are certified. -/
theorem star_triangle_dichotomy (w : Wiring.Choice) :
    IsGreatest (attainableScores w)
      (if Wiring.isStar w then 1 / 2 + (1 + Real.sqrt 33) / 24 else 3 / 4) := by
  constructor
  · refine ⟨3, Relabel.transport w (Attainment.attainingReplacement (Relabel.geometry w)), ?_⟩
    rw [Relabel.wiring_score]
    unfold Relabel.geometry
    split
    · exact Attainment.attain_star
    · exact Attainment.attain_triangle
  · rintro s ⟨n, R, rfl⟩
    exact Relabel.every_wiring_ceiling w R

#print axioms star_triangle_dichotomy
end FourSpin
