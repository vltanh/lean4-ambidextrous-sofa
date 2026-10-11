module

public import AmbidextrousSofa.Analysis.CanonicalWingChord
public import AmbidextrousSofa.Analysis.HorizontalLeakageScalar
public import AmbidextrousSofa.Analysis.FullTriangleWidth

@[expose] public section

/-!
# The actual horizontal one-turn obstruction for a leakage bound

The ordinary body is the actual niche-cut survivor of the cap. Its
connectedness, passage, area identity and wing chord estimate have already
been proved. Endpoint stationarity now replaces the two actual endpoint
heights by an upper bound for the two actual middle-endpoint niches.
This yields the scalar inequality contradicted by every leakage row.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- Any actual leakage row rules out the corresponding actual horizontal
maximum. The remaining analytical input is only the endpoint leakage
estimate, not an area or sharpness assertion. -/
theorem IsFullCapMaximizer.false_of_horizontal_leakage_row
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ} (R : HorizontalLeakageRow)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 ≤ C) (haC : R.a ≤ C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1)
    (hnL : sweptNiche U (Real.pi / 2) (-C) ≤ R.B)
    (hnR : sweptNiche U (Real.pi / 2) C ≤ R.B) : False := by
  have hC1 := hU.quarter_width_lt_thirty_seven_fiftieths
  rw [capWidth, hl, hr] at hC1
  have haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := ⟨0, 1, by simpa using hmiddle⟩
  have hleft : capRoof U (-C) = 1 :=
    hmiddle (-C) (by rw [middleHalfInterval_eq_centered hl hr]; exact ⟨le_rfl, by linarith⟩)
  have hright : capRoof U C = 1 :=
    hmiddle C (by rw [middleHalfInterval_eq_centered hl hr]; exact ⟨by linarith, le_rfl⟩)
  have hnecessary := hU.ordinary_area_chord_necessary_of_canonical_range (h := 0) hl hr
    (by simpa using hleft) hright hC0 (by linarith) le_rfl (by norm_num) hheight haffine
  have hsum := hU.endpoint_height_sum_of_affine hheight haffine
  rw [(centered_quarter_points hl hr).1, (centered_quarter_points hl hr).2.1, hleft,
    hright] at hsum
  set E := capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)
  simp only [zero_div, mul_zero, sub_zero] at hnecessary
  have hroot := Real.sqrt_le_sqrt (show C ^ 2 + (1 - R.B) ^ 2 / 4 ≤ C ^ 2 + (1 - E / 2) ^ 2 by
    nlinarith [mul_nonneg (show 0 ≤ (1 - E / 2) - (1 - R.B) / 2 by linarith)
      (show 0 ≤ (1 - E / 2) + (1 - R.B) / 2 by linarith [R.B_le_one])])
  have hlinear := mul_le_mul_of_nonneg_left (show 2 - R.B ≤ 3 - E by linarith)
    (by linarith : 0 ≤ C)
  exact R.not_ordinary_area_bound haC (by linarith)

end AmbidextrousSofa
