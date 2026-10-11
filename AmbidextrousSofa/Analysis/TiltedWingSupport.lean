module

public import AmbidextrousSofa.Analysis.LeftCompanionDensity
public import AmbidextrousSofa.Analysis.ShadowCurvature
public import AmbidextrousSofa.Analysis.NegativeCornerCurvature
public import AmbidextrousSofa.Analysis.SupportDensityCalculus

@[expose] public section

/-!
# The literal support geometry at the start of a tilted wing

Before the middle normal, the original companion support is attained at
the high middle point, whereas the actual left cut is supported at the
low middle point. After the middle normal the cut and original supports
and right tangents agree. In the canonical width and tilt range the
original corner is strictly below the floor before that normal.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem tilted_initial_coefficient_nonneg {m t : ℝ}
    (ht0 : 0 ≤ t) (htm : t ≤ Real.arctan m) :
    0 ≤ m * Real.cos t - Real.sin t := by
  have htL := htm.trans_lt (Real.arctan_lt_pi_div_two m)
  have h := Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos], htL⟩
    ⟨Real.neg_pi_div_two_lt_arctan m, Real.arctan_lt_pi_div_two m⟩ htm
  rw [Real.tan_arctan, Real.tan_eq_sin_div_cos,
    div_le_iff₀ (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htL⟩)] at h
  linarith

/-- The high middle point is an actual supporting point throughout
the initial original companion arc. -/
theorem IsDownwardCap.companionSupport_eq_high_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hhigh : capRoof U b = 1)
    (hs : 0 ≤ Real.sin t) (hc : 0 ≤ Real.cos t)
    (hcoef : 0 ≤ m * Real.cos t - Real.sin t) :
    angleSupport U (t + Real.pi / 2) = -b * Real.sin t + Real.cos t := by
  rw [angleSupport, ← companionNormal_eq_unitNormal]
  have hline := congrArg (· * Real.cos t) ((haffine b ⟨hab.le, le_rfl⟩).symm.trans hhigh)
  refine support_eq_of_mem hU.isCompact (fun p hp => ?_) (capRoof_mem hU.isCompact hb)
    (by simp only [coordDot, companionNormal, hhigh]; ring)
  simp only [coordDot, companionNormal]
  by_cases hbp : b ≤ p.1
  · linarith [mul_le_mul_of_nonneg_right (hU.inStrip hp).2 hc,
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbp) hs]
  · linarith [mul_le_mul_of_nonneg_right ((le_capRoof hU.isCompact hp).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp, rfl⟩)) hc,
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hbp)) hcoef]

/-- The same initial directions support the literal left cut at its
low middle point. The joining direction is included. -/
theorem IsDownwardCap.companionSupport_leftCut_eq_low_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hc : 0 ≤ Real.cos t) (hcoef : 0 ≤ m * Real.cos t - Real.sin t) :
    angleSupport (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2) =
      -a * Real.sin t + capRoof U a * Real.cos t := by
  rw [angleSupport, ← companionNormal_eq_unitNormal]
  have hline := congrArg (· * Real.cos t) (haffine a ⟨le_rfl, hab.le⟩)
  refine support_eq_of_mem (hU.leftCompanionCap ha).isCompact (fun p hp => ?_)
    (hU.rightRoof_mem_leftCompanionCap ha) (by simp only [coordDot, companionNormal]; ring)
  simp only [coordDot, companionNormal]
  linarith [mul_le_mul_of_nonneg_right ((le_capRoof hU.isCompact hp.1).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)) hc,
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp.2.2) hcoef]

theorem IsDownwardCap.companionSupport_and_tangent_leftCut_after_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (htm : Real.arctan m ≤ t) (ht0 : 0 ≤ t) (htL : t < Real.pi / 2) :
    angleSupport (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2) =
        angleSupport U (t + Real.pi / 2) ∧
      supportTangent (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2) =
        supportTangent U (t + Real.pi / 2) := by
  have hv := hU.vplus_leftCompanionCap_eq_of_affine (t := t + Real.pi / 2) ha hb hab haffine
    (Real.sin_pos_of_pos_of_lt_pi (by linarith only [ht0, Real.pi_pos]) (by linarith only [htL]))
    (affineNormal_coefficient_nonpos_after (by unfold affineNormalAngle; linarith only [htm])
      (by linarith only [htL]))
  refine ⟨?_, by simp only [supportTangent, hv]⟩
  change MovingSofaOptimality.supp _ _ = MovingSofaOptimality.supp _ _
  rw [← MovingSofaOptimality.dot_vplus_uvec, ← MovingSofaOptimality.dot_vplus_uvec, hv]

/-- The canonical rectangle and tilt bounds imply the strict margin
which puts the initial original corner below the floor. -/
theorem canonical_width_add_slope_lt_one {C h : ℝ}
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h < 17 / 50) :
    C + h / (2 * C) < 1 := by
  have := (div_lt_iff₀ (by linarith only [hC0])).mpr
    (show h < (1 - C) * (2 * C) by nlinarith only [hC0, hC1, hh])
  linarith only [this]

/-- This is the original cap's corner, with its original high-point
companion support. It is not the corner obtained by substituting the
low-wing cut. -/
theorem IsDownwardCap.attachedCorner_neg_before_positive_affine
    {U : Set Plane} (hU : IsDownwardCap U) {C m c t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hhigh : capRoof U C = 1) (ht : t ∈ Ioo (0 : ℝ) (Real.arctan m)) :
    (attachedCorner U t).2 < 0 := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨ht.1, ht.2.trans (Real.arctan_lt_pi_div_two m)⟩
  have ha : -C ∈ horizontalProjection U :=
    hU.horizontalProjection_eq_Icc ▸ ⟨by linarith, by linarith⟩
  have hb : C ∈ horizontalProjection U :=
    hU.horizontalProjection_eq_Icc ▸ ⟨by linarith, by linarith⟩
  have hcoef := tilted_initial_coefficient_nonneg ht.1.le ht.2.le
  have hcos : 1 - Real.cos t ≤ m * Real.sin t := by
    nlinarith only [mul_nonneg hcoef hs.le, Real.sin_sq_add_cos_sq t, Real.cos_le_one t, hc]
  have hf : angleSupport U t ≤ 2 * C * Real.cos t + Real.sin t :=
    hU.support_unitNormal_le_centeredBox (hU.subset_centeredBox_of_endpoints hl hr) hs.le hc.le
  rw [attachedCorner_snd_eq_support,
    hU.companionSupport_eq_high_of_affine ha hb (by linarith) haffine hhigh hs.le hc.le hcoef]
  linarith only [mul_le_mul_of_nonneg_right hf hs.le, hcos,
    mul_le_mul_of_nonneg_left (Real.cos_le_one t) (mul_nonneg hC.le hs.le),
    mul_neg_of_neg_of_pos (show C + m - 1 < 0 by linarith only [hsmall]) hs,
    Real.sin_sq_add_cos_sq t]

end AmbidextrousSofa
