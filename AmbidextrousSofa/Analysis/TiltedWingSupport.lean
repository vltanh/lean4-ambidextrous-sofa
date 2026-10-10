module

public import AmbidextrousSofa.Analysis.FullCompanionDensity
public import AmbidextrousSofa.Analysis.NegativeCornerCurvature
public import AmbidextrousSofa.Analysis.SupportDensityCalculus

@[expose] public section

/-!
# The literal support geometry at the start of a tilted wing

Before the middle normal, the original companion support is attained at
the high middle point, whereas the actual left cut is supported at the
low middle point. After the middle normal the cut and original supports
and right tangents agree. In the canonical width and tilt range the
original corner is strictly below the floor before that normal, so the
original first-wing curvature vanishes there by actual source occupation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem tilted_initial_coefficient_nonneg {m t : ℝ}
    (ht0 : 0 ≤ t) (htm : t ≤ Real.arctan m) :
    0 ≤ m * Real.cos t - Real.sin t := by
  have htθ : t + Real.pi / 2 ≤ affineNormalAngle m := by
    unfold affineNormalAngle
    linarith only [htm]
  rcases htθ.eq_or_lt with heq | hlt
  · have hz := affineNormalAngle_zero m
    rw [← heq, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at hz
    linarith only [hz]
  · have h := affineNormal_coefficient_pos_before
      (show 0 ≤ t + Real.pi / 2 by linarith only [ht0, Real.pi_pos]) hlt
    rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at h
    linarith only [h]

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
  change support U (unitNormal (t + Real.pi / 2)) = _
  rw [← companionNormal_eq_unitNormal]
  have hline : m * b + c = 1 := (haffine b ⟨hab.le, le_rfl⟩).symm.trans hhigh
  refine support_eq_of_mem hU.isCompact ?_
    (q := (b, capRoof U b)) (capRoof_mem hU.isCompact hb) ?_
  · intro p hp
    by_cases hbp : b ≤ p.1
    · have hh := mul_le_mul_of_nonneg_right (hU.inStrip hp).2 hc
      have hx := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbp) hs
      dsimp only [coordDot, companionNormal]
      nlinarith only [hh, hx]
    · have hroof : p.2 ≤ m * p.1 + c :=
        (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp)).trans
          (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp, rfl⟩)
      have hh := mul_le_mul_of_nonneg_right hroof hc
      have hx := mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_not_ge hbp)) hcoef
      have heq := congrArg (fun r : ℝ => r * Real.cos t) hline
      dsimp only [coordDot, companionNormal]
      nlinarith only [hh, hx, heq]
  · simp only [coordDot, companionNormal, hhigh, one_mul]
    ring

/-- The same initial directions support the literal left cut at its
low middle point. The joining direction is included. -/
theorem IsDownwardCap.companionSupport_leftCut_eq_low_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hc : 0 ≤ Real.cos t) (hcoef : 0 ≤ m * Real.cos t - Real.sin t) :
    angleSupport (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2) =
      -a * Real.sin t + capRoof U a * Real.cos t := by
  have hV := hU.leftCompanionCap ha
  change support (AmbidextrousSofa.leftCompanionCap U a) (unitNormal (t + Real.pi / 2)) = _
  rw [← companionNormal_eq_unitNormal]
  have hline := haffine a ⟨le_rfl, hab.le⟩
  refine support_eq_of_mem hV.isCompact ?_ (hU.rightRoof_mem_leftCompanionCap ha) ?_
  · intro p hp
    have hroof : p.2 ≤ m * p.1 + c :=
      (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp.1)).trans
        (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
    have hh := mul_le_mul_of_nonneg_right hroof hc
    have hx := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp.2.2) hcoef
    have heq := congrArg (fun r : ℝ => r * Real.cos t) hline
    dsimp only [coordDot, companionNormal]
    nlinarith only [hh, hx, heq]
  · dsimp only [coordDot, companionNormal]
    ring

theorem IsDownwardCap.companionSupport_and_tangent_leftCut_after_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (htm : Real.arctan m ≤ t) (ht0 : 0 ≤ t) (htL : t < Real.pi / 2) :
    angleSupport (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2) =
        angleSupport U (t + Real.pi / 2) ∧
      supportTangent (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2) =
        supportTangent U (t + Real.pi / 2) := by
  have hθ0 : 0 < t + Real.pi / 2 := by linarith only [ht0, Real.pi_pos]
  have hθπ : t + Real.pi / 2 < Real.pi := by linarith only [htL]
  have hθm : affineNormalAngle m ≤ t + Real.pi / 2 := by
    unfold affineNormalAngle
    linarith only [htm]
  have hv := hU.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine
    (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
    (affineNormal_coefficient_nonpos_after hθm hθπ.le)
  constructor
  · change MovingSofaOptimality.supp (AmbidextrousSofa.leftCompanionCap U a) _ = MovingSofaOptimality.supp U _
    rw [← MovingSofaOptimality.dot_vplus_uvec, ← MovingSofaOptimality.dot_vplus_uvec, hv]
  · simp only [supportTangent, hv]

theorem IsDownwardCap.companionTangent_leftCut_before_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (ht0 : 0 ≤ t) (htm : t < Real.arctan m) :
    supportTangent (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2) =
      -a * Real.cos t - capRoof U a * Real.sin t := by
  have hθ0 : 0 < t + Real.pi / 2 := by linarith only [ht0, Real.pi_pos]
  have hθm : t + Real.pi / 2 < affineNormalAngle m := by
    unfold affineNormalAngle
    linarith only [htm]
  have hv := hU.vplus_leftCompanionCap_eq_rightRoof_of_positive_coefficient
    ha hb hab haffine
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (hθm.trans (affineNormalAngle_mem m).2))
    (affineNormal_coefficient_pos_before hθ0.le hθm)
  rw [supportTangent, hv]
  dsimp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec]
  rw [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  ring

/-- The canonical rectangle and tilt bounds imply the strict margin
which puts the initial original corner below the floor. -/
theorem canonical_width_add_slope_lt_one {C h : ℝ}
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h < 17 / 50) :
    C + h / (2 * C) < 1 := by
  have h2C : 0 < 2 * C := by linarith only [hC0]
  have hprod := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hC1) (show 0 ≤ C - 13 / 50 by linarith only [hC0])
  have htilt : h < (1 - C) * (2 * C) := by nlinarith only [hprod, hh]
  have hdiv := (div_lt_iff₀ h2C).mpr htilt
  linarith only [hdiv]

theorem one_sub_cos_le_slope_mul_sin {m t : ℝ}
    (hs : 0 ≤ Real.sin t) (hc : 0 < Real.cos t)
    (hcoef : 0 ≤ m * Real.cos t - Real.sin t) :
    1 - Real.cos t ≤ m * Real.sin t := by
  have hsin := mul_nonneg hcoef hs
  have hcircle := Real.sin_sq_add_cos_sq t
  have hcle := Real.cos_le_one t
  apply (mul_le_mul_iff_left₀ hc).mp
  nlinarith only [hsin, hcircle, hcle]

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
  have htL : t < Real.pi / 2 := ht.2.trans (Real.arctan_lt_pi_div_two m)
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [htL, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], htL⟩
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hcoef := tilted_initial_coefficient_nonneg ht.1.le ht.2.le
  have hg := hU.companionSupport_eq_high_of_affine ha hb (by linarith) haffine
    hhigh hs.le hc.le hcoef
  have hf : angleSupport U t ≤ 2 * C * Real.cos t + Real.sin t :=
    hU.support_unitNormal_le_centeredBox (hU.subset_centeredBox_of_endpoints hl hr) hs.le hc.le
  have hfs := mul_le_mul_of_nonneg_right hf hs.le
  have hcos := one_sub_cos_le_slope_mul_sin hs.le hc hcoef
  have hCs := mul_le_mul_of_nonneg_left (Real.cos_le_one t) (mul_nonneg hC.le hs.le)
  have hstrict := mul_neg_of_neg_of_pos (show C + m - 1 < 0 by linarith only [hsmall]) hs
  have hcircle := Real.sin_sq_add_cos_sq t
  rw [attachedCorner_snd_eq_support, hg]
  nlinarith only [hfs, hcos, hCs, hstrict, hcircle]

/-- Actual source occupation supplies the initial zero-curvature
interval of a positively tilted full maximizer. -/
theorem IsFullCapMaximizer.first_wing_curvature_zero_before_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hm : 0 ≤ m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) (hhigh : capRoof U C = 1) :
    upperCurvature U (Ioo (0 : ℝ) (Real.arctan m)) = 0 := by
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hsub : Ioo (0 : ℝ) (Real.arctan m) ⊆
      {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} := by
    intro t ht
    have htL := ht.2.trans (Real.arctan_lt_pi_div_two m)
    refine ⟨firstQuarter_subset_regularCurvatureDomain_of_nonneg hm ⟨ht.1, htL⟩, ?_⟩
    rw [sourceCornerHeight, sourceQuarterAngle, if_pos htL]
    exact hU.isCap.attachedCorner_neg_before_positive_affine hl hr hC hsmall haff hhigh ht
  exact le_antisymm ((measure_mono hsub).trans_eq
    (hU.upperCurvature_negative_corners_eq_zero hheight haffine)) zero_le

end AmbidextrousSofa
