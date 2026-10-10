import AmbidextrousSofa.Analysis.CanonicalWingChord
import AmbidextrousSofa.Analysis.HorizontalLeakageScalar
import AmbidextrousSofa.Analysis.FullTriangleWidth

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

theorem IsFullCapMaximizer.horizontal_ordinary_area_necessary
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C B : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1)
    (hB1 : B ≤ 1)
    (hnL : sweptNiche U (Real.pi / 2) (-C) ≤ B)
    (hnR : sweptNiche U (Real.pi / 2) C ≤ B) :
    C * (2 - B) + Real.sqrt (C ^ 2 + (1 - B) ^ 2 / 4) ≤
      (22199 : ℝ) / 10000 := by
  have haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c := by
    refine ⟨0, 1, ?_⟩
    intro x hx
    simpa only [zero_mul, zero_add] using hmiddle x hx
  have hminus : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C := by
    rw [hl, hr]
    ring
  have hplus : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C := by
    rw [hl, hr]
    ring
  have hleft : capRoof U (-C) = 1 := hmiddle (-C) (by
    rw [middleHalfInterval_eq_centered hl hr]
    exact ⟨le_rfl, by linarith⟩)
  have hright : capRoof U C = 1 := hmiddle C (by
    rw [middleHalfInterval_eq_centered hl hr]
    exact ⟨by linarith, le_rfl⟩)
  have hnecessary := hU.ordinary_area_chord_necessary_of_canonical_range
    (h := 0) hl hr (by simpa only [sub_zero] using hleft) hright hC0 hC1
    (by norm_num) (by norm_num) hheight haffine
  have hsum := hU.endpoint_height_sum_of_affine hheight haffine
  rw [hminus, hplus, hleft, hright] at hsum
  let E := capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)
  have hEB : E ≤ 1 + B := by dsimp [E]; linarith
  have hdrop0 : 0 ≤ (1 - B) / 2 := by linarith
  have hdrop : (1 - B) / 2 ≤ 1 - E / 2 := by linarith
  have hdropSq := (sq_le_sq₀ hdrop0 (hdrop0.trans hdrop)).2 hdrop
  have hroot : Real.sqrt (C ^ 2 + (1 - B) ^ 2 / 4) ≤
      Real.sqrt (C ^ 2 + (1 - E / 2) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left
    (show 2 - B ≤ 3 - E by linarith) (by linarith : 0 ≤ C)
  dsimp only [E] at hroot hlinear
  norm_num only [zero_div, mul_zero, sub_zero] at hnecessary
  linarith

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
  have hquarter : capWidth U / 4 = C := by dsimp [capWidth]; rw [hl, hr]; ring
  have hC1 := hU.quarter_width_lt_thirty_seven_fiftieths
  rw [hquarter] at hC1
  exact R.not_ordinary_area_bound haC
    (hU.horizontal_ordinary_area_necessary hl hr hC0 hC1.le hheight hmiddle R.B_le_one hnL hnR)

end AmbidextrousSofa
