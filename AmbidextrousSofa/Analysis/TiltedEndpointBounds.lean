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
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hab : -C < C := by linarith only [hC0]
  have hV := hU.leftCompanionCap ha
  have hline : m * (-C) + c = 1 - h :=
    (haffine (-C) ⟨le_rfl, hab.le⟩).symm.trans hlow
  apply sweptNiche_le_of_forall (by linarith only [Real.pi_pos]) (le_max_right _ _)
  intro t ht
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hsupport : support (AmbidextrousSofa.leftCompanionCap U (-C)) (companionNormal t) ≤
      2 * C * Real.sin t + (1 - h) * Real.cos t := by
    apply support_le_of_forall hV.nonempty
    intro p hp
    have hxlo : -2 * C ≤ p.1 := by simpa only [hl] using hp.2.1
    have hroof : p.2 ≤ m * p.1 + c :=
      (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp.1)).trans
        (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
    have hpy : p.2 ≤ 1 - h := by
      have hx := mul_le_mul_of_nonneg_left hp.2.2 hm
      linarith only [hroof, hx, hline]
    have hx := mul_le_mul_of_nonneg_right hxlo hs.le
    have hy := mul_le_mul_of_nonneg_right hpy hc.le
    dsimp only [coordDot, companionNormal]
    nlinarith only [hx, hy]
  have hcircle := horizontal_box_circle_bound (s := Real.cos t) (c := Real.sin t)
    hC0.le hC1 (Real.sin_sq_add_cos_sq t)
  have hwall : secondWall (AmbidextrousSofa.leftCompanionCap U (-C)) t (-C) ≤
      Analysis.tiltedBoxHeight C - h := by
    rw [secondWall, div_le_iff₀ hc]
    unfold Analysis.tiltedBoxHeight
    nlinarith only [hsupport, hcircle]
  exact (min_le_right (firstWall U t (-C)) (secondWall U t (-C))).trans
    ((hU.secondWall_le_leftCompanionCap ha hb hab haffine hab.le hs.le hc).trans
      (max_le_max_right 0 hwall))

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
  have h := hU.centered_endpoint_laws (a := 2 * C) hheight
    (by rw [hl]; ring) hr
    (by simpa only [show -(2 * C) / 2 = -C by ring] using hlow)
    (by simpa only [show 2 * C / 2 = C by ring] using hhigh)
    ⟨m, c, by simpa only [show -(2 * C) / 2 = -C by ring,
      show 2 * C / 2 = C by ring] using haffine⟩
  simpa only [hl, hr, show -(2 * C) / 2 = -C by ring,
    show 2 * C / 2 = C by ring, show -(2 * C) = -2 * C by ring] using h

/-- All bounds refer to the original right endpoint and original niche.
The stronger lower bound keeps the low-wing floor clipping until the
small-height hypothesis makes its unclipped bound nonnegative. -/
theorem IsFullCapMaximizer.tilted_endpoint_momentum_bounds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h < 17 / 50)
    (hm : 0 ≤ m) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    -7 / 12 < capRoof U (horizontalRight U) - 1 + h ∧
      capRoof U (horizontalRight U) - 1 + h < 7 / 40 ∧
      capRoof U (horizontalRight U) - 1 + h ≤ -1 / 4 + 5 * h / 4 ∧
      (h ≤ 1 / 8 → -7 / 12 + 3 * h / 2 ≤
        capRoof U (horizontalRight U) - 1 + h) := by
  have hEP := (hU.tilted_endpoint_laws hl hr hheight haffine hlow hhigh).1
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0.le
    (by linarith only [hC1])
  have hlowbox := hU.isCap.left_middle_niche_le_tilted_box hl hr hC0
    (by linarith only [hC1]) hm haffine hlow
  have hH := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths hC0.le hC1
  change sweptNiche U (Real.pi / 2) (-C) ≤ Analysis.tiltedBoxHeight C ∧
    sweptNiche U (Real.pi / 2) C ≤ Analysis.tiltedBoxHeight C at hn
  have hz0 := sweptNiche_nonneg U (Real.pi / 2) C
  have hw0 := sweptNiche_nonneg U (Real.pi / 2) (-C)
  have hBlo : -7 / 12 < capRoof U (horizontalRight U) - 1 + h := by
    linarith only [hEP, hn.1, hH, hh0, hz0]
  have hBhi : capRoof U (horizontalRight U) - 1 + h ≤ -1 / 4 + 5 * h / 4 := by
    linarith only [hEP, hn.2, hH, hw0]
  refine ⟨hBlo, by linarith only [hBhi, hh1], hBhi, ?_⟩
  intro hhsmall
  have hw : sweptNiche U (Real.pi / 2) (-C) ≤ 1 / 3 - h :=
    hlowbox.trans (max_le (by linarith only [hH]) (by linarith only [hhsmall]))
  linarith only [hEP, hw, hz0]

end AmbidextrousSofa
