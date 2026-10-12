module

public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.LeftCompanionCap
public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds
public import AmbidextrousSofa.Analysis.WideWidthExclusion

@[expose] public section

/-!
# Actual endpoint bounds for a positively tilted cap

The literal low-wing cut lies below the low middle height. Its box wall
therefore improves the left middle niche bound by the full height drop,
with the floor clipping retained. The actual endpoint pressure equations
then give the momentum intervals needed by the initial excess estimates.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.left_middle_niche_le_tilted_box
    {U : Set Plane} (hU : IsDownwardCap U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) :
    sweptNiche U (Real.pi / 2) (-C) ≤
      max (Analysis.tiltedBoxHeight C - h) 0 := by
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [hU.horizontalProjection_eq_Icc, hl, hr]
  have ha : -C ∈ horizontalProjection U := hproj ▸ ⟨by linarith, by linarith⟩
  have hb : C ∈ horizontalProjection U := hproj ▸ ⟨by linarith, by linarith⟩
  have hab : -C < C := by linarith
  have hline := (haffine (-C) ⟨le_rfl, hab.le⟩).symm.trans hlow
  refine sweptNiche_le_of_forall (by positivity) (le_max_right _ _) fun t ht => ?_
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  have hsupport : support (AmbidextrousSofa.leftCompanionCap U (-C)) (companionNormal t) ≤
      2 * C * Real.sin t + (1 - h) * Real.cos t := by
    refine support_le_of_forall (hU.leftCompanionCap ha).nonempty fun p hp => ?_
    have hpy : p.2 ≤ 1 - h := by
      linarith [(le_capRoof hU.isCompact hp.1).trans (hU.capRoof_le_affine_of_affine_segment ha hb
        hab haffine p.1 ⟨p, hp.1, rfl⟩), mul_le_mul_of_nonneg_left hp.2.2 hm]
    simp only [coordDot, companionNormal]
    linarith [mul_le_mul_of_nonneg_right (hl ▸ hp.2.1 : -2 * C ≤ p.1) hs.le,
      mul_le_mul_of_nonneg_right hpy hc.le]
  refine (min_le_right _ _).trans ((hU.secondWall_le_leftCompanionCap ha hb hab haffine hab.le
    hs.le hc).trans (max_le_max_right 0 ?_))
  rw [secondWall, div_le_iff₀ hc, Analysis.tiltedBoxHeight]
  linarith [horizontal_box_circle_bound (s := Real.cos t) (c := Real.sin t) hC0.le hC1
    (Real.sin_sq_add_cos_sq t)]

theorem IsFullCapMaximizer.tilted_endpoint_laws
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    capRoof U (horizontalRight U) = 1 / 2 + h / 4 +
      (3 * sweptNiche U (Real.pi / 2) C - sweptNiche U (Real.pi / 2) (-C)) / 4 ∧
    capRoof U (horizontalLeft U) = 1 / 2 - 3 * h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (-C) - sweptNiche U (Real.pi / 2) C) / 4 := by
  have e1 : -(2 * C) / 2 = -C := by ring
  have e2 : 2 * C / 2 = C := by ring
  have h := hU.centered_endpoint_laws (a := 2 * C) hheight (by rw [hl]; ring) hr
    (by rwa [e1]) (by rwa [e2]) ⟨m, c, by rwa [e1, e2]⟩
  rw [hl, hr, neg_mul]
  simpa only [e1, e2] using h

/-- All bounds refer to the original right endpoint and original niche.
The stronger lower bound keeps the low-wing floor clipping until the
small-height hypothesis makes its unclipped bound nonnegative. -/
theorem IsFullCapMaximizer.tilted_endpoint_momentum_bounds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h < 1 / 3)
    (hm : 0 ≤ m) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    -7 / 12 < capRoof U (horizontalRight U) - 1 + h ∧
      capRoof U (horizontalRight U) - 1 + h < 7 / 40 ∧
      capRoof U (horizontalRight U) - 1 + h ≤ -1 / 4 + 5 * h / 4 ∧
      (h ≤ 1 / 8 → -7 / 12 + 3 * h / 2 ≤
        capRoof U (horizontalRight U) - 1 + h) := by
  have hEP := (hU.tilted_endpoint_laws hl hr hheight haffine hlow hhigh).1
  obtain ⟨hn1, hn2⟩ : sweptNiche U (Real.pi / 2) (-C) ≤ Analysis.tiltedBoxHeight C ∧
      sweptNiche U (Real.pi / 2) C ≤ Analysis.tiltedBoxHeight C :=
    hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0.le (by linarith)
  have hH := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths hC0.le hC1
  have hz0 := sweptNiche_nonneg U (Real.pi / 2) C
  have hw0 := sweptNiche_nonneg U (Real.pi / 2) (-C)
  refine ⟨by linarith, by linarith, by linarith, fun hhsmall => ?_⟩
  have := (hU.isCap.left_middle_niche_le_tilted_box hl hr hC0 (by linarith) hm haffine hlow).trans
    (max_le (c := 1 / 3 - h) (by linarith) (by linarith))
  linarith

end AmbidextrousSofa
