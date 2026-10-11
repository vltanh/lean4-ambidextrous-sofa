module

public import AmbidextrousSofa.Analysis.CompanionZero
public import AmbidextrousSofa.Analysis.TiltedWingSupport
public import AmbidextrousSofa.Analysis.NichePositiveMiddle

@[expose] public section

/-!
# The actual positive middle projection of a tilted cap

The zero of the literal low-wing companion envelope is the compact
minimum constructed in `CompanionZero`. To its left the niche vanishes.
To its right, a pinned high middle point makes every first wall positive
to the left of the shifted left baseline, and beyond that baseline the
actual top-point positivity lemma applies, so the niche is positive.
Strictly to its left, the original companion numerator is negative at
every angle except the initial axis, which is the source-cutoff input.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.capRoof_leftCompanionCap {U : Set Plane}
    (hU : IsDownwardCap U) {a x : ℝ} (ha : a ∈ horizontalProjection U)
    (hx : x ∈ Icc (horizontalLeft U) a) :
    capRoof (AmbidextrousSofa.leftCompanionCap U a) x = capRoof U x := by
  have hP := hU.horizontalProjection_eq_Icc
  rw [hP] at ha
  exact capRoof_horizontalCut hU ha.1 (hP ▸ Icc_subset_Icc le_rfl ha.2) hx

theorem IsDownwardCap.sweptNiche_eq_zero_of_le_low_wing_zero
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ y ∈ Icc a b, capRoof U y = m * y + c)
    (hxb : x ≤ b) (hx : x ≤ companionZero (AmbidextrousSofa.leftCompanionCap U a)) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  refine le_antisymm (sweptNiche_le_of_forall (by linarith only [Real.pi_pos]) le_rfl
    fun t ht => (min_le_right _ _).trans ?_) (sweptNiche_nonneg _ _ _)
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  exact (hU.secondWall_le_leftCompanionCap ha hb hab haffine hxb hs.le hc).trans
    (max_le ((hU.leftCompanionCap ha).secondWall_nonpos_of_le_companionZero hx ht) le_rfl)

/-- Every middle point right of the low-wing zero has a positive niche. This uses actual support
points alone; no curvature or stationarity assumption is needed. -/
theorem IsDownwardCap.sweptNiche_pos_of_low_wing_zero_lt
    {U : Set Plane} (hU : IsDownwardCap U) {C x : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C) (hC : 2 / 3 ≤ C)
    (hhigh : capRoof U C = 1) (hVH : capHeight (AmbidextrousSofa.leftCompanionCap U (-C)) < 1)
    (hVL : 0 < capRoof (AmbidextrousSofa.leftCompanionCap U (-C))
      (horizontalLeft (AmbidextrousSofa.leftCompanionCap U (-C))))
    (hx : x ∈ Ioo (max (-C) (companionZero (AmbidextrousSofa.leftCompanionCap U (-C)))) C) :
    0 < sweptNiche U (Real.pi / 2) x := by
  have ha : -C ∈ horizontalProjection U :=
    hU.horizontalProjection_eq_Icc ▸ ⟨by linarith, by linarith⟩
  have hb : C ∈ horizontalProjection U :=
    hU.horizontalProjection_eq_Icc ▸ ⟨by linarith, by linarith⟩
  have hhighPoint : (C, 1) ∈ U := by simpa only [hhigh] using capRoof_mem hU.isCompact hb
  rcases le_or_gt x (1 - 2 * C) with hsplit | hsplit
  · -- Left of the shifted baseline, the low-wing second wall and the first wall are positive.
    obtain ⟨t, ht, hsecond⟩ := (hU.leftCompanionCap ha).exists_secondWall_pos_of_companionZero_lt
      hVH hVL ((le_max_right _ _).trans_lt hx.1)
    obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
    refine (lt_min ?_ (hsecond.trans_le (secondWall_mono (leftCompanionCap_subset U (-C))
      (hU.leftCompanionCap ha).nonempty hU.isCompact hc x))).trans_le
      (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) ht)
    have hsum : 1 < Real.cos t + Real.sin t := by
      nlinarith only [Real.sin_sq_add_cos_sq t, mul_pos hs hc, hs, hc]
    have hsupport : C * Real.cos t + 1 * Real.sin t ≤ support U (unitNormal t) :=
      coordDot_le_support hU.isCompact hhighPoint (unitNormal t)
    rw [firstWall]
    exact div_pos (by linarith only [hsupport, hsum,
      mul_le_mul_of_nonneg_right (by linarith only [hC, hsplit] : 1 ≤ C - x) hc.le]) hs
  · exact hU.sweptNiche_pos_of_top_point_right hhighPoint hx.2 (by rw [hl]; linarith only [hsplit])

def secondWallNumerator (U : Set Plane) (t x : ℝ) : ℝ :=
  support U (companionNormal t) - 1 + x * Real.sin t

/-- The undivided wall remains strictly negative at the terminal axis.
This closed-angle statement is what survives uniform Hausdorff limits. -/
theorem IsDownwardCap.secondWallNumerator_neg_of_lt_low_wing_zero
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ y ∈ Icc a b, capRoof U y = m * y + c)
    (hhigh : capRoof U b = 1) (hxb : x < b)
    (hx : x < companionZero (AmbidextrousSofa.leftCompanionCap U a))
    (hxaxis : x < horizontalLeft U + 1)
    (ht : t ∈ Ioc (0 : ℝ) (Real.pi / 2)) : secondWallNumerator U t x < 0 := by
  rw [secondWallNumerator]
  rcases ht.2.eq_or_lt with rfl | htL
  · simp only [companionNormal, Real.sin_pi_div_two, Real.cos_pi_div_two, mul_one]
    rw [support_horizontal_left hU.isCompact hU.nonempty]
    linarith only [hxaxis]
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨ht.1, htL⟩
  by_cases htm : t ≤ Real.arctan m
  · have hg := hU.companionSupport_eq_high_of_affine ha hb hab haffine hhigh hs.le hc.le
      (tilted_initial_coefficient_nonneg ht.1.le htm)
    simp only [angleSupport, ← companionNormal_eq_unitNormal] at hg
    rw [hg]
    linarith only [mul_neg_of_neg_of_pos (sub_neg.mpr hxb) hs, Real.cos_le_one t]
  · have heq := (hU.companionSupport_and_tangent_leftCut_after_affine ha hb hab haffine
      (le_of_not_ge htm) ht.1.le htL).1
    simp only [angleSupport, ← companionNormal_eq_unitNormal] at heq
    simpa only [heq, zero_mul] using (div_lt_iff₀ hc).mp
      ((hU.leftCompanionCap ha).secondWall_neg_of_lt_companionZero hx ⟨ht.1, htL⟩)

end AmbidextrousSofa
