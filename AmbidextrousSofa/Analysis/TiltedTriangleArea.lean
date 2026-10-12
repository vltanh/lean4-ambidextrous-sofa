module

public import AmbidextrousSofa.Analysis.TiltedTriangleScalar
public import AmbidextrousSofa.Analysis.FullTriangleArea
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds
public import AmbidextrousSofa.Analysis.WideWidthExclusion

@[expose] public section

/-!
# Actual triangle exclusion with a dry low middle endpoint

The supports, exterior cuts, full niche gains, and floor losses all
belong to the original cap. The actual zero left niche sharpens only
the floor payment, and the joint support comparison applies to every
clipping case. No scalar upper bound on the score is a premise.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.false_of_radius_width_zero_left
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a h : ℝ}
    (ha0 : 2 * Analysis.tiltedRadiusWidth ≤ a) (ha1 : a ≤ 37 / 25)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hnzero : sweptNiche U (Real.pi / 2) (-a / 2) = 0) : False := by
  have haLower : (73 / 50 : ℝ) ≤ a := by
    have hlow := Analysis.tiltedRadiusWidth_bounds.1
    have hbracket := Analysis.tiltedRadius_comparison_brackets.1
    linarith
  obtain ⟨hEPR, hEPL⟩ := hU.centered_endpoint_laws hheight hl hr hleft hright haffine
  obtain ⟨hk0, hk1, hksq, hc0, hc1⟩ := fullTriangle_offset_bounds
  dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hn := sweptNiche_nonneg U (Real.pi / 2) (a / 2)
  have hnR : sweptNiche U (Real.pi / 2) (a / 2) ≤ 1 / 3 := by
    have hH : 1 - Real.sqrt (1 - (a / 2) ^ 2) < 33 / 100 :=
      Analysis.tiltedBoxHeight_lt_thirty_three_hundredths (by linarith only [haLower])
        (by linarith only [ha1])
    have := hU.isCap.middle_niche_le_box_height_of_box
      (hU.isCap.subset_centeredBox_of_endpoints (by rw [hl]; ring) (by rw [hr]; ring))
      (by linarith only [haLower]) (by linarith only [ha1] : a / 2 ≤ 1)
    linarith only [this.2, hH]
  obtain ⟨hq, hS⟩ := hU.isCap.threeAngleScore_le_full_triangles (by linarith only [haLower, hh1])
    (by linarith only [ha1]) (by linarith only [hh0]) (by linarith only [hh1]) hl hr hleft hright
    haffine (by linarith only [hEPR, hEPL, hn, hnzero])
  -- The zero left niche sharpens the bound on the left endpoint depth.
  have hloss := floor_loss_le_of_bounds (k := Real.sqrt 2 - 1)
    (t := 2 * fullTriangleCos (Real.sqrt 2 - 1) - (1 + (Real.sqrt 2 - 1))) (by linarith only [hk1])
    (by linarith only [hEPR, hnzero, hn] : 1 - capRoof U a ≤ 1 / 2 - h / 4)
    (by linarith only [hEPL, hnzero, hnR] : 1 - capRoof U (-a) ≤ 7 / 12 + 3 * h / 4)
  have hfin := tiltedTriangleRelaxation_add_loss_lt ha0 hh0 hh1
    (by linarith only [hk0]) hksq (by linarith only [hc0]) (fullTriangleCos_quadratic hksq) hq
  rw [tiltedTriangleLoss] at hfin
  linarith only [hU.reference_le, referenceHalfAreaLower_lt_half_M, hS, hloss, hfin,
    hU.isCap.capScore_le_threeAngleScore
      (sub_le_self _ (Real.arctan_pos.mpr (by linarith only [hk0])).le) le_rfl]

/-- The dry-endpoint triangle comparison supplies the same radius-width
bound to the selector and to the small-height ordinary-area argument. -/
theorem IsFullCapMaximizer.centered_width_lt_radiusWidth_of_dry
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hdry : sweptNiche U (Real.pi / 2) (-C) = 0) : C < Analysis.tiltedRadiusWidth := by
  by_contra! hwide
  have e1 : -(2 * C) / 2 = -C := by ring
  have e2 : 2 * C / 2 = C := by ring
  exact hU.false_of_radius_width_zero_left (a := 2 * C) (by linarith) (by linarith)
    hh0 hh1 (hl.trans (neg_mul 2 C)) hr hheight (by rwa [e1]) (by rwa [e2])
    ⟨m, c, by rwa [e1, e2]⟩ (by rwa [e1])

end AmbidextrousSofa
