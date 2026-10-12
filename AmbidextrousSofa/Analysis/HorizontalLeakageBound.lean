module

public import AmbidextrousSofa.Analysis.HorizontalLeakageOccupation
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.TiltedEndpointLeakage
public import AmbidextrousSofa.Analysis.FullTriangleWidth
public import AmbidextrousSofa.Analysis.CapReflection

@[expose] public section

/-!
# Horizontal curvature excess ends before endpoint contact

The preliminary width cut gives one uniform stopping estimate. After
`11/15` the density is at most one. The wall at the middle endpoint is
then nonpositive from `arccos C` onwards; before that angle it increases.
The swept niche is therefore zero at that endpoint. Reflection gives the
other endpoint, and stationarity fixes both axis heights at one half.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.horizontal_right_endpoint_niche_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) (hC : 2 / 3 < C) :
    sweptNiche U (Real.pi / 2) C = 0 := by
  have hC0 : 0 ≤ C := by linarith
  have hwidth : capWidth U = 4 * C := by rw [capWidth, hl, hr]; ring
  have hC1 : C ≤ 37 / 50 := by
    have h := hU.quarter_width_lt_thirty_seven_fiftieths
    rw [hwidth] at h
    linarith
  have he := (hU.horizontal_endpoint_laws hl hr hC0 hheight hmiddle).1
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0 (by linarith)
  obtain ⟨he0, hcross, henergy⟩ := horizontal_excess_stopping_bounds hC.le hC1
    (e := capRoof U (horizontalRight U))
    (by linarith [hn.1, sweptNiche_nonneg U (Real.pi / 2) C])
    (by linarith [hn.2, sweptNiche_nonneg U (Real.pi / 2) (-C)])
  obtain ⟨ρ, hρ, hb, hK, heq, -⟩ :=
    hU.horizontal_curvature_density_corner_controls hheight hmiddle
  obtain ⟨A, hA, henvelope⟩ := hU.exists_horizontal_quadratic_excess_envelope
    (h := 1 / 3) (T := 2 / 5) hheight hmiddle hwidth hC he0 hρ
    (fun s => (hb s).1) hK (fun s => (hb s).2) heq
    (by norm_num) (by norm_num) (by norm_num) hcross henergy
  have hunit : ∀ᵐ s ∂volume.restrict (Ioo (11 / 15 : ℝ) (Real.pi / 2)), ρ s ≤ 1 := by
    have henv := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo (by norm_num : (0 : ℝ) ≤ 11 / 15) le_rfl) henvelope
    filter_upwards [henv, ae_restrict_mem measurableSet_Ioo] with s hs hmem
    have hout : s ∉ Icc A (A + 1 / 3) := by
      intro hin
      linarith [hA.2, hmem.1, hin.2]
    simp only [horizontalLeakageEnvelope, indicator_of_notMem hout] at hs
    linarith
  have htop := hU.top_vminus_pi_div_two hheight hmiddle
  rw [capWidth, (centered_quarter_points hl hr).2.1] at htop
  have hzero := hU.isCap.middle_niche_le_top_overhang_of_late_unit hρ
    (fun s => (hb s).1) hK heq (by
      intro s hs
      apply mem_regularCurvatureDomain_iff.mpr
      exact ⟨hs.1, by linarith [hs.2, Real.pi_pos], ne_of_lt hs.2,
        by simpa using (sin_cos_pos_of_mem_quarter hs).2.ne'⟩)
    hr (by linarith) hC1 le_rfl htop hunit
  simp only [sub_self, zero_mul, zero_div] at hzero
  exact le_antisymm hzero (sweptNiche_nonneg U (Real.pi / 2) C)

theorem IsFullCapMaximizer.horizontal_endpoint_niches_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) (hC : 2 / 3 < C) :
    sweptNiche U (Real.pi / 2) (-C) = 0 ∧ sweptNiche U (Real.pi / 2) C = 0 := by
  obtain ⟨hl', hr', hheight', hmid⟩ :=
    hU.isCap.horizontalMirror_centered rfl hl hr hheight hmiddle
  have hleft := hU.horizontalMirror.horizontal_right_endpoint_niche_eq_zero
    hl' hr' hheight' hmid hC
  exact ⟨by simpa only [sweptNiche_horizontalMirror] using hleft,
    hU.horizontal_right_endpoint_niche_eq_zero hl hr hheight hmiddle hC⟩

theorem IsFullCapMaximizer.horizontal_axis_heights_eq_half
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) (hC : 2 / 3 < C) :
    capRoof U (horizontalRight U) = 1 / 2 ∧ capRoof U (horizontalLeft U) = 1 / 2 := by
  have hn := hU.horizontal_endpoint_niches_eq_zero hl hr hheight hmiddle hC
  simpa [hn.1, hn.2] using hU.horizontal_endpoint_laws hl hr (by linarith) hheight hmiddle

end AmbidextrousSofa
