module

public import AmbidextrousSofa.Analysis.FirstUnitNiche
public import AmbidextrousSofa.Analysis.FirstSourceFlux
public import AmbidextrousSofa.Measure.SignedRoofIntegral

@[expose] public section

/-!
# Actual positive core contacts

The inner corner of the actual support pair moves with the two momenta.
Where the first momentum is negative and the second positive, it moves
strictly left. The first tangent is monotone on the complete quarter;
the literal cut companion tangent is monotone on any prefix with unit
companion density. These orders make the angle of a positive core point
the unique maximizer of the original clipped wall family. The original
companion wall is compared with the literal cut at every angle,
including angles before the affine normal.

A strict horizontal displacement of the first tangent forces a strict
height loss, and every maximizing angle at a positive first-tangent
contact has the same tangent abscissa.
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

/-- The point `z` lies on the swept niche, and `t` is the only angle whose clipped wall
attains the niche over the abscissa of `z`. -/
abbrev UniqueNicheContact {U : Set Plane} (hU : IsDownwardCap U) (z : Plane) (t : ℝ) : Prop :=
  sweptNiche U (Real.pi / 2) z.1 = z.2 ∧ ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip hU.toCompactCap z.1 s = sweptNiche U (Real.pi / 2) z.1 → s = t

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

open scoped ActualPair

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
    (Real.hasDerivAt_cos t) (sin_cos_pos_of_mem_quarter ht).2.ne'
  simp only [secondWall, companionNormal_eq_unitNormal]
  refine hd.congr_deriv ?_
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  simp only [Pi.add_apply]
  congr 1
  linear_combination x * Real.sin_sq_add_cos_sq t

theorem fullTiltedSupportQuarterPair_walls_core {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    firstWall U t (Z t).1 = (Z t).2 ∧ secondWall V t (Z t).1 = (Z t).2 := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  rw [firstWall, secondWall, companionNormal_eq_unitNormal, div_eq_iff hs.ne', div_eq_iff hc.ne']
  constructor
  · show (F).f t - 1 - _ = _
    dsimp only [innerCornerPoint]
    linear_combination (1 - (F).f t) * Real.sin_sq_add_cos_sq t
  · show (F).g t - 1 + _ = _
    dsimp only [innerCornerPoint]
    linear_combination (1 - (F).g t) * Real.sin_sq_add_cos_sq t

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
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter htq
  exact sub_neg.mpr ((mul_neg_of_neg_of_pos (hphase t ht).1 hc).trans (mul_pos (hphase t ht).2 hs))

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
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  refine ⟨hwalls.1, le_antisymm ?_ (hwalls.2 ▸ secondWall_mono (leftCompanionCap_subset _ _)
    hU.isCap_fullLeftCompanion.nonempty hU.isCap.isCompact hc _)⟩
  simpa only [hwalls.2, max_eq_left hy.le] using hU.isCap.secondWall_le_leftCompanionCap
    ha hb hab haffine hx hs.le hc

/-- The high middle point makes every original companion wall
nonpositive before and at the affine normal. Thus a positive middle
core lies strictly after that normal, not at its omitted atom. -/
theorem fullTiltedSupportQuarterPair_positive_core_after_affine
    (hhigh : capRoof U (horizontalRight U - capWidth U / 4) = 1)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) : Real.arctan m < t := by
  refine lt_of_not_ge fun hnot => hy.not_ge ?_
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
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
    UniqueNicheContact hU.isCap (Z t) t := by
  have hwalls := fullTiltedSupportQuarterPair_original_walls_core
    hU hm haffine hρ hρ0 hρK heq ht hy hx
  have hcorner : cornerWall U t (Z t).1 = (Z t).2 := by
    rw [cornerWall, hwalls.1, hwalls.2, min_self]
  -- After `t`, the first wall over `(Z t).1` strictly decreases in the angle.
  have hafter (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hts : t < s) :
      firstWall U s (Z t).1 < (Z t).2 := by
    have hgap : (Z t).1 < (B t).1 := by
      linarith [innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD t,
        mul_neg_of_neg_of_pos hp (sin_cos_pos_of_mem_quarter ht).1]
    rw [← hwalls.1]
    refine endpoint_lt_of_hasDerivAt_neg hts (fun r hr =>
      fullTiltedSupportQuarterPair_first_wall_derivative hU hm haffine hρ hρ0 hρK heq
        ⟨ht.1.trans_le hr.1, hr.2.trans_lt hs.2⟩ _) fun r hr => ?_
    have hrq : r ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
    exact div_neg_of_neg_of_pos (sub_neg.mpr (hgap.trans_le
      ((fullTiltedSupportQuarterPair_first_tangent_order hU hm haffine hρ hρ0 hρK heq hunit).1
        (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self hrq) hr.1.le)))
      (pow_pos (sin_cos_pos_of_mem_quarter hrq).1 2)
  have hstrict (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hne : s ≠ t) :
      cornerWall U s (Z t).1 < (Z t).2 := by
    rcases lt_or_gt_of_ne hne with hst | hts
    · obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
        (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
      exact (min_le_right _ _).trans_lt ((hU.isCap.secondWall_le_leftCompanionCap ha hb hab
        haffine hx (sin_cos_pos_of_mem_quarter hs).1.le (sin_cos_pos_of_mem_quarter hs).2).trans_lt
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
    UniqueNicheContact hU.isCap (Z t) t := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1, ht.2.trans_le hτ.2⟩
  have hgap : (D t).1 < (Z t).1 := by
    linarith [innerCorner_fst_eq_secondTangent (F).f (F).g (F).gD t,
      mul_pos hq (sin_cos_pos_of_mem_quarter htq).2]
  -- On the companion-unit prefix the second tangent moves right.
  obtain ⟨-, -, hDx, -, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hDmono : MonotoneOn (fun t => (D t).1) (Icc 0 τ) := by
    apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
      (hDx.mono (uIcc_subset_uIcc_left (Icc_subset_uIcc hτ))) hτ.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hτ.2) hderiv,
      hcompanion, ae_restrict_mem measurableSet_Ioo] with t hdt hu ht
    exact ⟨hdt.2.2.1, mul_nonneg (sub_nonneg.mpr hu) (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [ht.1, Real.pi_pos]) (ht.2.le.trans hτ.2))⟩
  -- Before `t`, the cut wall over `(Z t).1` strictly increases in the angle.
  refine fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls
    hU hm haffine hρ hρ0 hρK heq hunit htq hp hy hx fun s hs => ?_
  rw [← (fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq htq).2]
  refine endpoint_lt_of_hasDerivAt_pos hs.2 (fun r hr =>
    fullTiltedSupportQuarterPair_cut_wall_derivative hU hm haffine hρ hρ0 hρK heq
      ⟨hs.1.trans_le hr.1, hr.2.trans_lt htq.2⟩ _) fun r hr => ?_
  have hrq : r ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hs.1.trans hr.1, hr.2.trans htq.2⟩
  exact div_pos (sub_pos.mpr ((hDmono ⟨hrq.1.le, hr.2.le.trans ht.2.le⟩
    (Ioo_subset_Icc_self ht) hr.2.le).trans_lt hgap)) (pow_pos (sin_cos_pos_of_mem_quarter hrq).2 2)

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
  obtain ⟨hsin, hcos⟩ := sin_cos_pos_of_mem_quarter ht
  by_contra! hnot
  linarith [hmono (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst,
    mul_pos hcos (sub_pos.mpr hmove), mul_nonpos_of_nonneg_of_nonpos hsin.le hnot,
    mul_nonneg hsin.le (fullTiltedSupportQuarterPair_first_tangent_nonneg
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
  have hz := hlocal.hasDerivAt_eq_zero
    (fullTiltedSupportQuarterPair_first_wall_derivative hU hm haffine hρ hρ0 hρK heq hsq (B t).1)
  rw [div_eq_zero_iff, sub_eq_zero] at hz
  exact ⟨hsq, (hz.resolve_right (pow_ne_zero 2 (sin_cos_pos_of_mem_quarter hsq).1.ne')).symm⟩

end ActualPair

end AmbidextrousSofa
