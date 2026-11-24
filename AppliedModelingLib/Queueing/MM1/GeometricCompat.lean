import Mathlib.Probability.Distributions.Geometric

/-!
# Compatibility shim for the Mathlib v4.30.0 geometric-measure refactor

Mathlib v4.30.0 changed `ProbabilityTheory.geometricMeasure` to take
`p : unitInterval` and to be defined as a sum of Diracs, deprecating
`geometricPMF`. This file restores the earlier `PMF`-based measure under a new
name, so the M/M/1 proofs keep their statements, and records that it agrees
with the new Mathlib measure.
-/

set_option linter.deprecated false

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory

/-- The geometric law with success probability `p`, as the measure of
`geometricPMF` (the pre-v4.30.0 Mathlib definition of `geometricMeasure`). -/
noncomputable def geometricMeasureOld {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    Measure ℕ :=
  (geometricPMF hp_pos hp_le_one).toMeasure

instance isProbabilityMeasure_geometricMeasureOld {p : ℝ} (hp_pos : 0 < p)
    (hp_le_one : p ≤ 1) : IsProbabilityMeasure (geometricMeasureOld hp_pos hp_le_one) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- The old and new Mathlib geometric measures agree. -/
theorem geometricMeasureOld_eq_geometricMeasure {p : ℝ} (hp_pos : 0 < p)
    (hp_le_one : p ≤ 1) :
    geometricMeasureOld hp_pos hp_le_one = geometricMeasure ⟨p, hp_pos.le, hp_le_one⟩ := by
  have hp0 : (⟨p, hp_pos.le, hp_le_one⟩ : unitInterval) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp at this
    linarith
  refine Measure.ext_of_singleton fun n => ?_
  rw [geometricMeasureOld, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n),
    geometricMeasure_singleton hp0]
  rfl

end AppliedModelingLib.Probability
