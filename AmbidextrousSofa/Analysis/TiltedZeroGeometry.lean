module

public import AmbidextrousSofa.Analysis.CompanionZero
public import AmbidextrousSofa.Analysis.TiltedWingSupport
public import AmbidextrousSofa.Analysis.NichePositiveMiddle

@[expose] public section

/-!
# The actual positive middle projection of a tilted cap

The zero of the literal low-wing companion envelope is the compact
minimum constructed in `CompanionZero`. A pinned high middle point makes
every first wall positive to the left of the shifted left baseline.
Beyond that baseline the actual top-point positivity lemma applies.
Consequently the positive middle projection is one explicit interval.
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
  have ha' := ha
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at ha'
  exact capRoof_horizontalCut hU ha'.1
    (by rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
        exact Icc_subset_Icc le_rfl ha'.2) hx

theorem IsDownwardCap.firstWall_pos_of_high_middle_point
    {U : Set Plane} (hU : IsDownwardCap U) {C x t : ℝ}
    (hC : 2 / 3 ≤ C) (hhigh : (C, 1) ∈ U)
    (hx : x ≤ 1 - 2 * C) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < firstWall U t x := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hsum : 1 < Real.cos t + Real.sin t := by
    by_contra hnot
    have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
      (show 0 ≤ 1 + (Real.cos t + Real.sin t) by linarith only [hs, hc])
    nlinarith only [Real.sin_sq_add_cos_sq t, mul_pos hs hc, hprod]
  have hgap : 1 ≤ C - x := by linarith only [hC, hx]
  have hmul := mul_le_mul_of_nonneg_right hgap hc.le
  have hsupport : C * Real.cos t + 1 * Real.sin t ≤ support U (unitNormal t) :=
    coordDot_le_support hU.isCompact hhigh (unitNormal t)
  rw [firstWall]
  apply div_pos _ hs
  nlinarith only [hsupport, hmul, hsum]

theorem IsDownwardCap.sweptNiche_eq_zero_of_le_low_wing_zero
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ y ∈ Icc a b, capRoof U y = m * y + c)
    (hxb : x ≤ b) (hx : x ≤ companionZero (AmbidextrousSofa.leftCompanionCap U a)) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  apply le_antisymm _ (sweptNiche_nonneg _ _ _)
  apply sweptNiche_le_of_forall (by linarith only [Real.pi_pos]) le_rfl
  intro t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hlow := (hU.leftCompanionCap ha).secondWall_nonpos_of_le_companionZero hx ht
  exact (min_le_right _ _).trans
    ((hU.secondWall_le_leftCompanionCap ha hb hab haffine hxb hs.le hc).trans
      (max_le hlow le_rfl))

/-- This conclusion uses actual support points alone. No curvature or
stationarity assumption is needed to identify the positive interval. -/
theorem IsDownwardCap.sweptNiche_pos_iff_low_wing_zero_lt
    {U : Set Plane} (hU : IsDownwardCap U) {C m c x : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 2 / 3 ≤ C) (hm : 0 < m)
    (haffine : ∀ y ∈ Icc (-C) C, capRoof U y = m * y + c)
    (hhigh : capRoof U C = 1) (hlow : capRoof U (-C) < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) (hx : x ∈ Ioo (-C) C) :
    0 < sweptNiche U (Real.pi / 2) x ↔ companionZero (AmbidextrousSofa.leftCompanionCap U (-C)) < x := by
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hab : -C < C := by linarith only [hC]
  have hV := hU.leftCompanionCap ha
  have hVheight : capHeight (AmbidextrousSofa.leftCompanionCap U (-C)) < 1 := by
    rw [(hU.top_leftCompanionCap_of_positive_affine ha hb hab hm haffine).1]
    exact hlow
  have hVleft : 0 < capRoof (AmbidextrousSofa.leftCompanionCap U (-C))
      (horizontalLeft (AmbidextrousSofa.leftCompanionCap U (-C))) := by
    rw [horizontalLeft_leftCompanionCap hU ha,
      hU.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact hleft
  have hhighPoint : (C, 1) ∈ U := by
    simpa only [hhigh] using capRoof_mem hU.isCompact hb
  constructor
  · intro hpositive
    by_contra hnot
    rw [hU.sweptNiche_eq_zero_of_le_low_wing_zero ha hb hab haffine hx.2.le
      (le_of_not_gt hnot)] at hpositive
    exact lt_irrefl 0 hpositive
  · intro hz
    by_cases hsplit : x ≤ 1 - 2 * C
    · obtain ⟨t, ht, hsecond⟩ := hV.exists_secondWall_pos_of_companionZero_lt
        hVheight hVleft hz
      have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
      have hsecondU := hsecond.trans_le
        (secondWall_mono (leftCompanionCap_subset U (-C)) hV.nonempty hU.isCompact hc x)
      exact (lt_min (hU.firstWall_pos_of_high_middle_point hC hhighPoint hsplit ht)
        hsecondU).trans_le (cornerWall_le_sweptNiche
          (sweptWallValues_bddAbove hU.isCompact le_rfl x) ht)
    · exact hU.sweptNiche_pos_of_top_point_right hhighPoint hx.2
        (by rw [hl]; linarith only [lt_of_not_ge hsplit])

theorem IsDownwardCap.positive_middle_eq_low_wing_interval
    {U : Set Plane} (hU : IsDownwardCap U) {C m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 2 / 3 ≤ C) (hm : 0 < m)
    (haffine : ∀ y ∈ Icc (-C) C, capRoof U y = m * y + c)
    (hhigh : capRoof U C = 1) (hlow : capRoof U (-C) < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) :
    Ioo (-C) C ∩ {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x} =
      Ioo (max (-C) (companionZero (AmbidextrousSofa.leftCompanionCap U (-C)))) C := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨max_lt hx.1 ((hU.sweptNiche_pos_iff_low_wing_zero_lt hl hr hC hm haffine
      hhigh hlow hleft hx).mp hp), hx.2⟩
  · intro hx
    have hxJ : x ∈ Ioo (-C) C := ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩
    exact ⟨hxJ, (hU.sweptNiche_pos_iff_low_wing_zero_lt hl hr hC hm haffine
      hhigh hlow hleft hxJ).mpr ((le_max_right _ _).trans_lt hx.1)⟩

def secondWallNumerator (U : Set Plane) (t x : ℝ) : ℝ :=
  support U (companionNormal t) - 1 + x * Real.sin t

theorem IsDownwardCap.secondWall_neg_of_lt_low_wing_zero
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ y ∈ Icc a b, capRoof U y = m * y + c)
    (hhigh : capRoof U b = 1) (hxb : x < b)
    (hx : x < companionZero (AmbidextrousSofa.leftCompanionCap U a))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) : secondWall U t x < 0 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  by_cases htm : t ≤ Real.arctan m
  · have hg := hU.companionSupport_eq_high_of_affine ha hb hab haffine hhigh hs.le hc.le
      (tilted_initial_coefficient_nonneg ht.1.le htm)
    have hsupport : support U (companionNormal t) = -b * Real.sin t + Real.cos t := by
      simpa only [angleSupport, ← companionNormal_eq_unitNormal] using hg
    rw [secondWall, hsupport]
    apply div_neg_of_neg_of_pos _ hc
    have hgap := mul_neg_of_neg_of_pos (sub_neg.mpr hxb) hs
    nlinarith only [hgap, Real.cos_le_one t]
  · have heq := (hU.companionSupport_and_tangent_leftCut_after_affine ha hb hab haffine
      (le_of_not_ge htm) ht.1.le ht.2).1
    have hsupport : support (AmbidextrousSofa.leftCompanionCap U a) (companionNormal t) =
        support U (companionNormal t) := by
      simpa only [angleSupport, ← companionNormal_eq_unitNormal] using heq
    have hlow := (hU.leftCompanionCap ha).secondWall_neg_of_lt_companionZero hx ht
    simpa only [secondWall, hsupport] using hlow

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
  rcases ht.2.eq_or_lt with htL | htL
  · rw [htL, secondWallNumerator]
    simp only [companionNormal, Real.sin_pi_div_two, Real.cos_pi_div_two,
      mul_one]
    rw [support_horizontal_left hU.isCompact hU.nonempty]
    linarith only [hxaxis]
  · have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [ht.1, Real.pi_pos], htL⟩
    have h := hU.secondWall_neg_of_lt_low_wing_zero ha hb hab haffine hhigh hxb hx
      ⟨ht.1, htL⟩
    rw [secondWallNumerator]
    simpa only [zero_mul] using (div_lt_iff₀ hc).mp h

end AmbidextrousSofa
