module

public import AmbidextrousSofa.Analysis.FirstUnitNiche
public import AmbidextrousSofa.Analysis.FirstSourceFlux
public import AmbidextrousSofa.Measure.SignedRoofIntegral

@[expose] public section

/-!
# Actual positive core contacts under a first-unit prefix

The first tangent is monotone on the complete quarter. The literal cut
companion tangent is monotone only on the stated prefix. These orders
put the opposite-sign core strictly inside the charged middle interval
and make its angle the unique maximizer of the original clipped wall
family. The original companion wall is compared with the literal cut
at every angle, including angles before the affine normal.

The resulting open spatial pieces retain all their actual maximizing
angles. No source equality or contact decomposition is an assumption.
-/

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem innerCorner_fst_eq_firstTangent (f g fD : ℝ → ℝ) (t : ℝ) :
    (innerCornerPoint f g t).1 = (firstTangentPoint f fD t).1 +
      supportP fD g t * Real.sin t := by
  unfold innerCornerPoint firstTangentPoint Reference.supportPoint supportP
  ring

theorem innerCorner_fst_eq_secondTangent (f g gD : ℝ → ℝ) (t : ℝ) :
    (innerCornerPoint f g t).1 = (secondTangentPoint g gD t).1 +
      supportQ gD f t * Real.cos t := by
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  unfold innerCornerPoint supportQ
  ring

private theorem sin_cos_pos {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    0 < Real.sin t ∧ 0 < Real.cos t :=
  ⟨Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩⟩

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "B" => firstTangentPoint (F).f (F).fD
local notation "D" => secondTangentPoint (F).g (F).gD
local notation "Z" => innerCornerPoint (F).f (F).g
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

/-- The actual closed support representatives give ordinary derivatives
at every interior angle, including the cut's joining normal. -/
theorem fullTiltedSupportQuarterPair_support_derivatives {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (F).f ((F).fD t) t ∧ HasDerivAt (F).g ((F).gD t) t := by
  obtain ⟨hf, hg⟩ : HasDerivWithinAt (F).f ((F).fD t) (Icc 0 (Real.pi / 2)) t ∧
      HasDerivWithinAt (F).g ((F).gD t) (Icc 0 (Real.pi / 2)) t :=
    supportQuarterPair_derivatives_on_closed _ _ _ _ _ _ _ _ _ _ t (Ioo_subset_Icc_self ht)
  exact ⟨hf.hasDerivAt (Icc_mem_nhds ht.1 ht.2), hg.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

theorem fullTiltedSupportQuarterPair_core_continuous :
    ContinuousOn (fun t => (Z t).1) (Icc 0 (Real.pi / 2)) ∧
      ContinuousOn (fun t => (Z t).2) (Icc 0 (Real.pi / 2)) :=
  ⟨(((F).continuous_f.sub continuousOn_const).mul Real.continuous_cos.continuousOn).sub
      (((F).continuous_g.sub continuousOn_const).mul Real.continuous_sin.continuousOn),
    (((F).continuous_f.sub continuousOn_const).mul Real.continuous_sin.continuousOn).add
      (((F).continuous_g.sub continuousOn_const).mul Real.continuous_cos.continuousOn)⟩

theorem fullTiltedSupportQuarterPair_core_hasDerivAt {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun s => (Z s).1) (p t * Real.cos t - q t * Real.sin t) t ∧
      HasDerivAt (fun s => (Z s).2) (p t * Real.sin t + q t * Real.cos t) t := by
  obtain ⟨hf, hg⟩ := fullTiltedSupportQuarterPair_support_derivatives
    hU hm haffine hρ hρ0 hρK heq ht
  refine ⟨(((hf.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
      ((hg.sub_const 1).mul (Real.hasDerivAt_sin t))).congr_deriv ?_,
    (((hf.sub_const 1).mul (Real.hasDerivAt_sin t)).add
      ((hg.sub_const 1).mul (Real.hasDerivAt_cos t))).congr_deriv ?_⟩ <;>
    (unfold supportP supportQ; ring)

theorem fullTiltedSupportQuarterPair_cut_wall_derivative {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (x : ℝ) :
    HasDerivAt (fun s => secondWall V s x)
      ((x - (D t).1) / Real.cos t ^ 2) t := by
  have hg := (fullTiltedSupportQuarterPair_support_derivatives hU hm haffine hρ hρ0 hρK heq ht).2
  have hd := ((hg.sub_const 1).add ((Real.hasDerivAt_sin t).const_mul x)).div
    (Real.hasDerivAt_cos t) (sin_cos_pos ht).2.ne'
  simp only [secondWall, companionNormal_eq_unitNormal]
  refine hd.congr_deriv ?_
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  simp only [Pi.add_apply]
  congr 1
  linear_combination x * Real.sin_sq_add_cos_sq t

theorem fullTiltedSupportQuarterPair_walls_core {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    firstWall U t (Z t).1 = (Z t).2 ∧ secondWall V t (Z t).1 = (Z t).2 := by
  rw [firstWall, secondWall, companionNormal_eq_unitNormal, div_eq_iff (sin_cos_pos ht).1.ne',
    div_eq_iff (sin_cos_pos ht).2.ne']
  constructor
  · show (F).f t - 1 - _ = _
    dsimp only [innerCornerPoint]
    linear_combination (1 - (F).f t) * Real.sin_sq_add_cos_sq t
  · show (F).g t - 1 + _ = _
    dsimp only [innerCornerPoint]
    linear_combination (1 - (F).g t) * Real.sin_sq_add_cos_sq t

theorem fullTiltedSupportQuarterPair_companion_tangent_order_on_prefix {τ : ℝ}
    (hτ : τ ∈ Icc 0 (Real.pi / 2))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 τ), v t ≤ 1) :
    MonotoneOn (fun t => (D t).1) (Icc 0 τ) := by
  obtain ⟨-, -, hDx, -, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
    (hDx.mono (uIcc_subset_uIcc_left (Icc_subset_uIcc hτ))) hτ.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hτ.2) hderiv,
    hunit, ae_restrict_mem measurableSet_Ioo] with t hdt hu ht
  exact ⟨hdt.2.2.1, mul_nonneg (sub_nonneg.mpr hu) (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [ht.1, Real.pi_pos]) (ht.2.le.trans hτ.2))⟩

theorem fullTiltedSupportQuarterPair_first_tangent_nonneg
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 2)) : 0 ≤ (B t).2 := by
  have hfloor : (B (Real.pi / 2)).2 = 0 := by
    simp only [firstTangentPoint, Reference.supportPoint, hheight,
      (fullTiltedSupportQuarterPair_base_traces hU hm haffine hρ hρ0 hρK heq).2.2.1,
      Real.sin_pi_div_two, Real.cos_pi_div_two, sub_self, zero_mul, mul_zero, zero_add]
  exact hfloor.ge.trans ((fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).2 ht ⟨by positivity, le_rfl⟩ ht.2)

theorem fullTiltedSupportQuarterPair_core_strictAntiOn {α τ : ℝ}
    (hα : 0 ≤ α) (hτ : τ ≤ Real.pi / 2)
    (hphase : ∀ t ∈ Ioo α τ, p t < 0 ∧ 0 < q t) :
    StrictAntiOn (fun t => (Z t).1) (Icc α τ) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc α τ)
    ((fullTiltedSupportQuarterPair_core_continuous hU hm haffine hρ hρ0 hρK heq).1.mono
      (Icc_subset_Icc hα hτ)) fun t ht => ?_
  rw [interior_Icc] at ht
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hα.trans_lt ht.1, ht.2.trans_le hτ⟩
  rw [(fullTiltedSupportQuarterPair_core_hasDerivAt hU hm haffine hρ hρ0 hρK heq htq).1.deriv]
  exact sub_neg.mpr ((mul_neg_of_neg_of_pos (hphase t ht).1 (sin_cos_pos htq).2).trans
    (mul_pos (hphase t ht).2 (sin_cos_pos htq).1))

theorem fullTiltedSupportQuarterPair_core_geometry {C h α τ t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hα : 0 ≤ α) (hτ : τ ∈ Icc 0 (Real.pi / 2)) (hpα : p α = 0)
    (hphase : ∀ s ∈ Ioo α τ, p s < 0 ∧ 0 < q s)
    (hcompanion : ∀ᵐ s ∂volume.restrict (Ioo 0 τ), v s ≤ 1)
    (ht : t ∈ Ioo α τ) :
    (Z t).1 ∈ Ioo (-C) C ∧ 0 < (Z t).2 ∧
      (Z t).1 < (B t).1 ∧ (D t).1 < (Z t).1 := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hα.trans_lt ht.1, ht.2.trans_le hτ.2⟩
  obtain ⟨hs, hc⟩ := sin_cos_pos htq
  obtain ⟨hp, hq⟩ := hphase t ht
  -- The corner starts at the first tangent point, left of `C`, and moves left.
  have hBxα : (B α).1 < C := lt_of_not_ge fun hB =>
    (fullTiltedSupportQuarterPair_first_momentum_neg_after_middle hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh hlow ⟨hα, ht.1.le.trans (ht.2.le.trans hτ.2)⟩ hB).2.ne hpα
  have hright : (Z t).1 < (Z α).1 := fullTiltedSupportQuarterPair_core_strictAntiOn
    hU hm haffine hρ hρ0 hρK heq hα hτ.2 hphase ⟨le_rfl, ht.1.le.trans ht.2.le⟩
    (Ioo_subset_Icc_self ht) ht.1
  rw [innerCorner_eq_firstTangent_of_momentum_zero hpα] at hright
  -- The second tangent starts at `-C` and moves right.
  have hDorder : (D 0).1 ≤ (D t).1 :=
    fullTiltedSupportQuarterPair_companion_tangent_order_on_prefix
      hU hm haffine hρ hρ0 hρK heq hτ hcompanion ⟨le_rfl, hτ.1⟩ ⟨htq.1.le, ht.2.le⟩ htq.1.le
  rw [(fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow).2.2.1] at hDorder
  have hDgap : (D t).1 < (Z t).1 := by
    rw [innerCorner_fst_eq_secondTangent (F).f (F).g (F).gD]
    exact lt_add_of_pos_right _ (mul_pos hq hc)
  refine ⟨⟨hDorder.trans_lt hDgap, hright.trans hBxα⟩, ?_, ?_, hDgap⟩
  · rw [innerCorner_snd_eq_firstTangent (F).f (F).g (F).fD]
    exact sub_pos.mpr ((mul_neg_of_neg_of_pos hp hc).trans_le
      (fullTiltedSupportQuarterPair_first_tangent_nonneg hU hm haffine hρ hρ0 hρK heq
        hheight hunit (Ioo_subset_Icc_self htq)))
  · rw [innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD]
    exact add_lt_of_neg_right _ (mul_neg_of_neg_of_pos hp hs)

/-- Positivity removes the harmless zero clip in the original-to-cut
comparison. Both original walls therefore pass through the literal
two-cap corner at every positive middle contact. -/
theorem fullTiltedSupportQuarterPair_original_walls_core {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) :
    firstWall U t (Z t).1 = (Z t).2 ∧ secondWall U t (Z t).1 = (Z t).2 := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hwalls := fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq ht
  refine ⟨hwalls.1, le_antisymm ?_ (hwalls.2 ▸ secondWall_mono (leftCompanionCap_subset _ _)
    hU.isCap_fullLeftCompanion.nonempty hU.isCap.isCompact (sin_cos_pos ht).2 _)⟩
  simpa only [hwalls.2, max_eq_left hy.le] using hU.isCap.secondWall_le_leftCompanionCap
    ha hb hab haffine hx (sin_cos_pos ht).1.le (sin_cos_pos ht).2

theorem fullTiltedSupportQuarterPair_core_eq_attachedCorner {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) :
    Z t = attachedCorner U t := by
  have h := (fullTiltedSupportQuarterPair_original_walls_core hU hm haffine hρ hρ0 hρK heq
    ht hy hx).2.trans (fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq
      ht).2.symm
  rw [secondWall, secondWall, div_left_inj' (sin_cos_pos ht).2.ne', add_left_inj,
    sub_left_inj] at h
  rw [attachedCorner, h, companionNormal_eq_unitNormal]
  rfl

/-- The high middle point makes every original companion wall
nonpositive before and at the affine normal. Thus a positive middle
core lies strictly after that normal, not at its omitted atom. -/
theorem fullTiltedSupportQuarterPair_positive_core_after_affine
    (hhigh : capRoof U (horizontalRight U - capWidth U / 4) = 1)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) : Real.arctan m < t := by
  refine lt_of_not_ge fun hnot => hy.not_ge ?_
  obtain ⟨hs, hc⟩ := sin_cos_pos ht
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  rw [← (fullTiltedSupportQuarterPair_original_walls_core hU hm haffine hρ hρ0 hρK heq
    ht hy hx).2, secondWall, companionNormal_eq_unitNormal]
  show (angleSupport U (t + Real.pi / 2) - 1 + _) / _ ≤ _
  rw [hU.isCap.companionSupport_eq_high_of_affine ha hb hab haffine hhigh hs.le hc.le
    (tilted_initial_coefficient_nonneg ht.1.le hnot)]
  have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hs.le
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [Real.cos_le_one t]) hc.le

theorem fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls {t : ℝ}
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hp : p t < 0)
    (hy : 0 < (Z t).2) (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4)
    (hEarlier : ∀ s ∈ Ioo 0 t, secondWall V s (Z t).1 < (Z t).2) :
    sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 ∧
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 s =
          sweptNiche U (Real.pi / 2) (Z t).1 → s = t) := by
  have hwalls := fullTiltedSupportQuarterPair_original_walls_core
    hU hm haffine hρ hρ0 hρK heq ht hy hx
  have hcorner : cornerWall U t (Z t).1 = (Z t).2 := by
    rw [cornerWall, hwalls.1, hwalls.2, min_self]
  -- After `t`, the first wall over `(Z t).1` strictly decreases in the angle.
  have hafter (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hts : t < s) :
      firstWall U s (Z t).1 < (Z t).2 := by
    have hgap : (Z t).1 < (B t).1 := by
      rw [innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD]
      exact add_lt_of_neg_right _ (mul_neg_of_neg_of_pos hp (sin_cos_pos ht).1)
    have hd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
        HasDerivAt (fun a => firstWall U a (Z t).1)
          (((Z t).1 - (B r).1) / Real.sin r ^ 2) r := by
      rw [fullTiltedSupportQuarterPair_first_tangency hU hm haffine hρ hρ0 hρK heq
        ⟨hr.1.le, hr.2⟩]
      exact hU.isCap.hasDerivAt_firstWall_of_open_first_density hρ hρ0 hρK heq
        (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hr _
    rw [← hwalls.1]
    refine endpoint_lt_of_hasDerivAt_neg hts
      (fun r hr => hd r ⟨ht.1.trans_le hr.1, hr.2.trans_lt hs.2⟩) fun r hr => ?_
    have hrq : r ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
    exact div_neg_of_neg_of_pos (sub_neg.mpr (hgap.trans_le
      ((fullTiltedSupportQuarterPair_first_tangent_order hU hm haffine hρ hρ0 hρK heq hunit).1
        (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self hrq) hr.1.le)))
      (pow_pos (sin_cos_pos hrq).1 2)
  have hstrict (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hne : s ≠ t) :
      cornerWall U s (Z t).1 < (Z t).2 := by
    rcases lt_or_gt_of_ne hne with hst | hts
    · obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
        (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
      exact (min_le_right _ _).trans_lt ((hU.isCap.secondWall_le_leftCompanionCap ha hb hab
        haffine hx (sin_cos_pos hs).1.le (sin_cos_pos hs).2).trans_lt
          (max_lt (hEarlier s ⟨hs.1, hst⟩) hy))
    · exact (min_le_left _ _).trans_lt (hafter s hs hts)
  have hN : sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 :=
    le_antisymm (sweptNiche_le_of_forall (by positivity) hy.le fun s hs =>
        (eq_or_ne s t).elim (fun he => he.symm ▸ hcorner.le) fun he => (hstrict s hs he).le)
      (hcorner ▸ cornerWall_le_sweptNiche
        (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl _) ht)
  refine ⟨hN, fun s hsc hmax => by_contra fun hne => ?_⟩
  rw [hN] at hmax
  rcases hsc.1.eq_or_lt with rfl | hs0
  · exact hy.ne' (hmax.symm.trans (fullWallClip_zero _ _))
  rcases hsc.2.eq_or_lt with rfl | hsL
  · exact hy.ne' (hmax.symm.trans (fullWallClip_pi_div_two _ _))
  exact (max_lt (hstrict s ⟨hs0, hsL⟩ hne) hy).ne hmax

theorem fullTiltedSupportQuarterPair_core_contact {τ t : ℝ}
    (hτ : τ ∈ Icc 0 (Real.pi / 2))
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (ht : t ∈ Ioo 0 τ) (hp : p t < 0) (hq : 0 < q t)
    (hy : 0 < (Z t).2) (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) :
    sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 ∧
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 s =
          sweptNiche U (Real.pi / 2) (Z t).1 → s = t) := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1, ht.2.trans_le hτ.2⟩
  have hgap : (D t).1 < (Z t).1 := by
    rw [innerCorner_fst_eq_secondTangent (F).f (F).g (F).gD]
    exact lt_add_of_pos_right _ (mul_pos hq (sin_cos_pos htq).2)
  -- Before `t`, the cut wall over `(Z t).1` strictly increases in the angle.
  refine fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls
    hU hm haffine hρ hρ0 hρK heq hunit htq hp hy hx fun s hs => ?_
  rw [← (fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq htq).2]
  refine endpoint_lt_of_hasDerivAt_pos hs.2 (fun r hr =>
    fullTiltedSupportQuarterPair_cut_wall_derivative hU hm haffine hρ hρ0 hρK heq
      ⟨hs.1.trans_le hr.1, hr.2.trans_lt htq.2⟩ _) fun r hr => ?_
  have hrq : r ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hs.1.trans hr.1, hr.2.trans htq.2⟩
  exact div_pos (sub_pos.mpr ((fullTiltedSupportQuarterPair_companion_tangent_order_on_prefix
    hU hm haffine hρ hρ0 hρK heq hτ hcompanion ⟨hrq.1.le, hr.2.le.trans ht.2.le⟩
    (Ioo_subset_Icc_self ht) hr.2.le).trans_lt hgap)) (pow_pos (sin_cos_pos hrq).2 2)

/-- A strict horizontal tangent displacement before the top requires
a strict height loss. This keeps open tangent pieces positive even
when the tangent parameterization contains plateaus. -/
theorem fullTiltedSupportQuarterPair_first_tangent_height_pos_of_abscissa_lt
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Ioo 0 (Real.pi / 2))
    (hst : s ≤ t) (hmove : (B s).1 < (B t).1) : 0 < (B s).2 := by
  obtain ⟨hBx, hBy, -, -, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  -- The projection of the tangent point on the normal at `t` decreases on `[s, t]`.
  have hmono : MonotoneOn (fun r => -(Real.sin t * (B r).2 + Real.cos t * (B r).1))
      (Icc s t) := by
    refine absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
      (d := fun r => (1 - ρ r) * Real.sin (t - r))
      (((hBy.const_mul (Real.sin t)).add (hBx.const_mul (Real.cos t))).neg.mono
        (uIcc_subset_uIcc (Icc_subset_uIcc hs) (Icc_subset_uIcc (Ioo_subset_Icc_self ht)))) hst ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hs.1 ht.2.le) hderiv,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hs.1 ht.2.le) hunit]
      with r hr hdr hur
    refine ⟨((hdr.2.1.const_mul (Real.sin t)).add (hdr.1.const_mul (Real.cos t))).neg.congr_deriv
      (by rw [Real.sin_sub]; ring), mul_nonneg (sub_nonneg.mpr hur)
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.2])
          (by linarith [hs.1, hr.1, ht.2, Real.pi_pos]))⟩
  have hsin := (sin_cos_pos ht).1.le
  by_contra! hnot
  linarith [hmono (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst,
    mul_pos (sin_cos_pos ht).2 (sub_pos.mpr hmove), mul_nonpos_of_nonneg_of_nonpos hsin hnot,
    mul_nonneg hsin (fullTiltedSupportQuarterPair_first_tangent_nonneg
      hU hm haffine hρ hρ0 hρK heq hheight hunit (Ioo_subset_Icc_self ht))]

/-- At a positive first-tangent contact every maximizing angle has the
same tangent abscissa. The maximizing set may be an angular interval. -/
theorem fullTiltedSupportQuarterPair_first_tangent_abscissa_of_maximizing_angle
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    {s t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (hp : p t ≤ 0) (hy : 0 < (B t).2)
    (hs : s ∈ Icc 0 (Real.pi / 2))
    (hmax : fullWallClip hU.isCap.toCompactCap (B t).1 s =
      sweptNiche U (Real.pi / 2) (B t).1) :
    s ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ (B s).1 = (B t).1 := by
  rw [fullTiltedSupportQuarterPair_niche_first_tangency hU hm haffine hρ hρ0 hρK heq
    hunit ht hp hy.le] at hmax
  have hsq : s ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
    refine ⟨hs.1.lt_of_ne ?_, hs.2.lt_of_ne ?_⟩ <;> rintro rfl
    · exact hy.ne' (hmax.symm.trans (fullWallClip_zero _ _))
    · exact hy.ne' (hmax.symm.trans (fullWallClip_pi_div_two _ _))
  have henvelope := fullTiltedSupportQuarterPair_first_wall_envelope
    hU hm haffine hρ hρ0 hρK heq hunit ht
  -- The first wall attains its envelope value at `s`, so `s` is a critical angle.
  have hvalue : firstWall U s (B t).1 = (B t).2 := le_antisymm (henvelope s hsq)
    ((le_of_not_gt fun h => (max_lt h hy).ne hmax).trans (min_le_left _ _))
  have hlocal : IsLocalMax (fun r => firstWall U r (B t).1) s :=
    eventually_of_mem (Ioo_mem_nhds hsq.1 hsq.2) fun r hr => (henvelope r hr).trans hvalue.ge
  have hz := hlocal.hasDerivAt_eq_zero (hU.isCap.hasDerivAt_firstWall_of_open_first_density
    hρ hρ0 hρK heq (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hsq (B t).1)
  rw [div_eq_zero_iff, sub_eq_zero, ← fullTiltedSupportQuarterPair_first_tangency
    hU hm haffine hρ hρ0 hρK heq ⟨hsq.1.le, hsq.2⟩] at hz
  exact ⟨hsq, (hz.resolve_right (pow_ne_zero 2 (sin_cos_pos hsq).1.ne')).symm⟩

theorem fullTiltedSupportQuarterPair_first_source_core_piece {C h α τ s t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hα : 0 ≤ α) (hτ : τ ∈ Icc 0 (Real.pi / 2)) (hpα : p α = 0)
    (hphase : ∀ r ∈ Ioo α τ, p r < 0 ∧ 0 < q r)
    (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (hs : s ∈ Ioo α τ) (ht : t ∈ Ioo α τ) (hst : s < t) :
    FirstSourceCorePiece hU.isCap Z s t := by
  have hmidL : horizontalLeft U + capWidth U / 4 = -C := by rw [capWidth, hl, hr]; ring
  have hmidR : horizontalRight U - capWidth U / 4 = C := by rw [capWidth, hl, hr]; ring
  have hsub : Icc s t ⊆ Ioo α τ := fun r hr => ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  have hquarter : Icc s t ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    fun r hr => ⟨hα.trans_lt (hsub hr).1, (hsub hr).2.trans_le hτ.2⟩
  have hgeometry (r : ℝ) (hrI : r ∈ Icc s t) :=
    fullTiltedSupportQuarterPair_core_geometry hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion (hsub hrI)
  have hcontact (r : ℝ) (hr : r ∈ Icc s t) :=
    fullTiltedSupportQuarterPair_core_contact hU hm haffine hρ hρ0 hρK heq hτ
      hunit hcompanion ⟨(hquarter hr).1, (hsub hr).2⟩ (hphase r (hsub hr)).1
      (hphase r (hsub hr)).2 (hgeometry r hr).2.1 (hmidR ▸ (hgeometry r hr).1.2.le)
  have hIVT (x : ℝ) (hx : x ∈ Ioo (Z t).1 (Z s).1) : ∃ r ∈ Icc s t, (Z r).1 = x :=
    intermediate_value_Icc' hst.le ((fullTiltedSupportQuarterPair_core_continuous
      hU hm haffine hρ hρ0 hρK heq).1.mono fun r hr => Ioo_subset_Icc_self (hquarter hr))
      (Ioo_subset_Icc_self hx)
  refine ⟨fullTiltedSupportQuarterPair_core_strictAntiOn hU hm haffine hρ hρ0 hρK heq
    hα hτ.2 hphase (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) hst,
    hmidL ▸ (hgeometry t ⟨hst.le, le_rfl⟩).1.1.le, hmidR ▸ (hgeometry s ⟨le_rfl, hst.le⟩).1.2.le,
    (hcontact s ⟨le_rfl, hst.le⟩).1, (hcontact t ⟨hst.le, le_rfl⟩).1,
    fun x hx => ?_, fun x hx a ha hmax => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    exact (hcontact r hr).1 ▸ (hgeometry r hr).2.1
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    rw [(hcontact r hr).2 a ha hmax]
    exact ⟨hr.1.lt_of_ne (by rintro rfl; exact lt_irrefl _ hx.2),
      hr.2.lt_of_ne (by rintro rfl; exact lt_irrefl _ hx.1)⟩

theorem fullTiltedSupportQuarterPair_first_source_charged_pieces {C h α τ β s t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hα : 0 ≤ α) (hτ : τ ∈ Icc 0 (Real.pi / 2)) (hpα : p α = 0)
    (hphase : ∀ r ∈ Ioo α τ, p r < 0 ∧ 0 < q r)
    (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (hβ : β ∈ Icc 0 (Real.pi / 2)) (hβx : (B β).1 = C)
    (hs : s ∈ Ioo α τ) (ht : t ∈ Ioo α τ) (hst : s < t) (htβ : t ≤ β) :
    FirstSourceChargedPieces hU.isCap B Z s t := by
  have hmidR : horizontalRight U - capWidth U / 4 = C := by rw [capWidth, hl, hr]; ring
  have hsub : Icc s t ⊆ Ioo α τ := fun r hr => ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  have hquarter : Icc s t ⊆ Icc (0 : ℝ) (Real.pi / 2) :=
    fun r hr => ⟨hα.trans (hsub hr).1.le, (hsub hr).2.le.trans hτ.2⟩
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
  have hB := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  have hopen (r : ℝ) (hr : r ∈ Icc s t) : r ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hα.trans_lt (hsub hr).1, (hsub hr).2.trans_le hτ.2⟩
  have hcontact (r : ℝ) (hr : r ∈ Icc s t) :=
    fullTiltedSupportQuarterPair_niche_first_tangency hU hm haffine hρ hρ0 hρK heq
      hunit (hopen r hr) (hphase r (hsub hr)).1.le
      (fullTiltedSupportQuarterPair_first_tangent_nonneg hU hm haffine hρ hρ0 hρK heq
        hheight hunit (hquarter hr))
  have hy (r : ℝ) (hr : r ∈ Icc s t) (hx : (B r).1 < (B t).1) : 0 < (B r).2 :=
    fullTiltedSupportQuarterPair_first_tangent_height_pos_of_abscissa_lt hU hm haffine hρ hρ0
      hρK heq hheight hunit (hquarter hr) (hopen t htI) hr.2 hx
  have hIVT (x : ℝ) (hx : x ∈ Ioo (B s).1 (B t).1) : ∃ r ∈ Icc s t, (B r).1 = x :=
    intermediate_value_Icc hst.le ((fullTiltedSupportQuarterPair_tangent_calculus
      hU hm haffine hρ hρ0 hρK heq).1.continuousOn.mono
        fun r hr => Icc_subset_uIcc (hquarter hr)) (Ioo_subset_Icc_self hx)
  refine ⟨fullTiltedSupportQuarterPair_first_source_core_piece hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion hs ht hst,
    hB (hquarter hsI) (hquarter htI) hst.le,
    (fullTiltedSupportQuarterPair_core_geometry hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion hs).2.2.1.le,
    hmidR ▸ hβx ▸ hB (hquarter htI) hβ htβ, hcontact s hsI, hcontact t htI,
    fun x hx => ?_, fun x hx a ha hmax => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    exact hcontact r hr ▸ hy r hr hx.2
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    have hangle := fullTiltedSupportQuarterPair_first_tangent_abscissa_of_maximizing_angle
      hU hm haffine hρ hρ0 hρK heq hunit (hopen r hr) (hphase r (hsub hr)).1.le (hy r hr hx.2)
      ha hmax
    exact ⟨lt_of_not_ge fun hle => hx.1.not_ge
        (hangle.2 ▸ hB (Ioo_subset_Icc_self hangle.1) (hquarter hsI) hle),
      lt_of_not_ge fun hle => hx.2.not_ge
        (hangle.2 ▸ hB (hquarter htI) (Ioo_subset_Icc_self hangle.1) hle)⟩

end ActualPair

end AmbidextrousSofa
