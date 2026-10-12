module

public import AmbidextrousSofa.Analysis.CanonicalWingChord
public import AmbidextrousSofa.Analysis.HorizontalLeakageBound

@[expose] public section

/-!
# A chord-area bound with dry middle endpoints

Stationarity fixes both axis heights at one half. Corner confinement
makes the niche convex on each exterior wing; its zero endpoint values
therefore make those wings dry. The actual ordinary survivor then has
area at least `2C + sqrt (C² + 1/4)`.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.horizontal_ordinary_area_bound
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) (hC : 2 / 3 < C) :
    2 * C + Real.sqrt (C ^ 2 + 1 / 4) ≤ (2.2199 : ℝ) := by
  have hC1 := hU.quarter_width_lt_thirty_seven_fiftieths
  rw [capWidth, hl, hr] at hC1
  have haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := ⟨0, 1, by simpa using hmiddle⟩
  have hleft : capRoof U (-C) = 1 :=
    hmiddle (-C) (by rw [(centered_quarter_points hl hr).2.2]; exact ⟨le_rfl, by linarith⟩)
  have hright : capRoof U C = 1 :=
    hmiddle C (by rw [(centered_quarter_points hl hr).2.2]; exact ⟨by linarith, le_rfl⟩)
  have hnecessary := hU.ordinary_area_chord_necessary_of_canonical_range (h := 0) hl hr
    (by simpa using hleft) hright (by linarith) (by linarith) le_rfl (by norm_num)
    hheight haffine
  obtain ⟨hR, hL⟩ := hU.horizontal_axis_heights_eq_half hl hr hheight hmiddle hC
  rw [hR, hL] at hnecessary
  norm_num at hnecessary
  nlinarith only [hnecessary]

end AmbidextrousSofa
