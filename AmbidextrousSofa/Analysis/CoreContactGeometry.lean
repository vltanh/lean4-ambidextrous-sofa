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

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

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

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "D" => secondTangentPoint (F).g (F).gD
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

/-- The actual closed support representatives give ordinary derivatives
at every interior angle, including the cut's joining normal. -/
theorem fullTiltedSupportQuarterPair_support_derivatives {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (F).f ((F).fD t) t ∧ HasDerivAt (F).g ((F).gD t) t := by
  have hd : ∀ s ∈ Icc 0 (Real.pi / 2),
      HasDerivWithinAt (F).f ((F).fD s) (Icc 0 (Real.pi / 2)) s ∧
        HasDerivWithinAt (F).g ((F).gD s) (Icc 0 (Real.pi / 2)) s := by
    unfold fullTiltedSupportQuarterPair
    exact supportQuarterPair_derivatives_on_closed _ _ _ _ _ _ _ _ _ _
  exact ⟨(hd t (Ioo_subset_Icc_self ht)).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2),
    (hd t (Ioo_subset_Icc_self ht)).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

theorem fullTiltedSupportQuarterPair_core_continuous :
    ContinuousOn (fun t => (Z t).1) (Icc 0 (Real.pi / 2)) ∧
      ContinuousOn (fun t => (Z t).2) (Icc 0 (Real.pi / 2)) := by
  exact ⟨(((F).continuous_f.sub continuousOn_const).mul Real.continuous_cos.continuousOn).sub
      (((F).continuous_g.sub continuousOn_const).mul Real.continuous_sin.continuousOn),
    (((F).continuous_f.sub continuousOn_const).mul Real.continuous_sin.continuousOn).add
      (((F).continuous_g.sub continuousOn_const).mul Real.continuous_cos.continuousOn)⟩

theorem fullTiltedSupportQuarterPair_core_hasDerivAt {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun s => (Z s).1) (p t * Real.cos t - q t * Real.sin t) t ∧
      HasDerivAt (fun s => (Z s).2) (p t * Real.sin t + q t * Real.cos t) t := by
  obtain ⟨hf, hg⟩ := fullTiltedSupportQuarterPair_support_derivatives
    hU hm haffine hρ hρ0 hρK heq ht
  constructor
  · apply (((hf.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
      ((hg.sub_const 1).mul (Real.hasDerivAt_sin t))).congr_deriv
    unfold supportP supportQ
    ring
  · apply (((hf.sub_const 1).mul (Real.hasDerivAt_sin t)).add
      ((hg.sub_const 1).mul (Real.hasDerivAt_cos t))).congr_deriv
    unfold supportP supportQ
    ring

theorem fullTiltedSupportQuarterPair_cut_wall_derivative {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (x : ℝ) :
    HasDerivAt (fun s => secondWall V s x)
      ((x - (D t).1) / Real.cos t ^ 2) t := by
  have hg := (fullTiltedSupportQuarterPair_support_derivatives
    hU hm haffine hρ hρ0 hρK heq ht).2
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hd : HasDerivAt (fun s => ((F).g s - 1 + x * Real.sin s) / Real.cos s) _ t :=
    ((hg.sub_const 1).add ((Real.hasDerivAt_sin t).const_mul x)).div
      (Real.hasDerivAt_cos t) hc
  have hfun : (fun s => ((F).g s - 1 + x * Real.sin s) / Real.cos s) =
      fun s => secondWall V s x := by
    funext s
    change (angleSupport V (s + Real.pi / 2) - 1 + x * Real.sin s) / Real.cos s = _
    simp only [secondWall, angleSupport, companionNormal_eq_unitNormal]
  rw [hfun] at hd
  apply hd.congr_deriv
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  apply congrArg (fun z : ℝ => z / Real.cos t ^ 2)
  dsimp only [Prod.fst, Pi.add_apply]
  nlinarith only [congrArg (fun z : ℝ => x * z) (Real.sin_sq_add_cos_sq t)]

theorem fullTiltedSupportQuarterPair_walls_core {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    firstWall U t (Z t).1 = (Z t).2 ∧ secondWall V t (Z t).1 = (Z t).2 := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).ne'
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩).ne'
  constructor
  · rw [firstWall, div_eq_iff hs]
    change (F).f t - 1 - (Z t).1 * Real.cos t = (Z t).2 * Real.sin t
    dsimp only [innerCornerPoint]
    nlinarith only [congrArg (fun z : ℝ => ((F).f t - 1) * z)
      (Real.sin_sq_add_cos_sq t)]
  · rw [secondWall, div_eq_iff hc, companionNormal_eq_unitNormal]
    change (F).g t - 1 + (Z t).1 * Real.sin t = (Z t).2 * Real.cos t
    dsimp only [innerCornerPoint]
    nlinarith only [congrArg (fun z : ℝ => ((F).g t - 1) * z)
      (Real.sin_sq_add_cos_sq t)]

theorem fullTiltedSupportQuarterPair_companion_tangent_order_on_prefix {τ : ℝ}
    (hτ : τ ∈ Icc 0 (Real.pi / 2))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 τ), v t ≤ 1) :
    MonotoneOn (fun t => (D t).1) (Icc 0 τ) ∧
      MonotoneOn (fun t => (D t).2) (Icc 0 τ) := by
  obtain ⟨_hBx, _hBy, hDx, hDy, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hsub : uIcc (0 : ℝ) τ ⊆ uIcc 0 (Real.pi / 2) := by
    simpa only [uIcc_of_le hτ.1, uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
      using Icc_subset_Icc le_rfl hτ.2
  have hd := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hτ.2) hderiv
  constructor
  · apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
      (hDx.mono hsub) hτ.1
    filter_upwards [hd, hunit, ae_restrict_mem measurableSet_Ioo] with t hdt hu ht
    exact ⟨hdt.2.2.1, mul_nonneg (sub_nonneg.mpr hu)
      (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith only [ht.1, Real.pi_pos]) (ht.2.le.trans hτ.2))⟩
  · apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
      (hDy.mono hsub) hτ.1
    filter_upwards [hd, hunit, ae_restrict_mem measurableSet_Ioo] with t hdt hu ht
    exact ⟨hdt.2.2.2, mul_nonneg (sub_nonneg.mpr hu)
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
        (by linarith only [ht.2, hτ.2, Real.pi_pos]))⟩

theorem fullTiltedSupportQuarterPair_first_tangent_nonneg
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 2)) : 0 ≤ (B t).2 := by
  have hfloor : (B (Real.pi / 2)).2 = 0 := by
    have hf := (fullTiltedSupportQuarterPair_base_traces hU hm haffine hρ hρ0 hρK heq).2.2.1
    simp only [firstTangentPoint, Reference.supportPoint, hf, hheight,
      Real.sin_pi_div_two, Real.cos_pi_div_two, sub_self, zero_mul, mul_zero, zero_add]
  have h := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).2 ht ⟨by positivity, le_rfl⟩ ht.2
  dsimp only at h
  rwa [hfloor] at h

theorem fullTiltedSupportQuarterPair_core_strictAntiOn {α τ : ℝ}
    (hα : 0 ≤ α) (hτ : τ ≤ Real.pi / 2)
    (hphase : ∀ t ∈ Ioo α τ, p t < 0 ∧ 0 < q t) :
    StrictAntiOn (fun t => (Z t).1) (Icc α τ) := by
  have hcont := (fullTiltedSupportQuarterPair_core_continuous
    hU hm haffine hρ hρ0 hρK heq).1.mono (Icc_subset_Icc hα hτ)
  apply strictAntiOn_of_deriv_neg (convex_Icc α τ) hcont
  intro t ht
  have ht' : t ∈ Ioo α τ := by simpa only [interior_Icc] using ht
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hα.trans_lt ht'.1, ht'.2.trans_le hτ⟩
  rw [(fullTiltedSupportQuarterPair_core_hasDerivAt hU hm haffine hρ hρ0 hρK heq htq).1.deriv]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htq.1
    (by linarith only [htq.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩
  exact sub_neg.mpr ((mul_neg_of_neg_of_pos (hphase t ht').1 hc).trans
    (mul_pos (hphase t ht').2 hs))

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
  have hαq : α ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨hα, ht.1.le.trans (ht.2.le.trans hτ.2)⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htq.1
    (by linarith only [htq.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩
  have hp := (hphase t ht).1
  have hq := (hphase t ht).2
  have hBxα : (B α).1 < C := by
    by_contra hnot
    have hnegative := (fullTiltedSupportQuarterPair_first_momentum_neg_after_middle
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hlow hαq
      (le_of_not_gt hnot)).2
    rw [hpα] at hnegative
    exact lt_irrefl 0 hnegative
  have hjoin : Z α = B α := innerCorner_eq_firstTangent_of_momentum_zero hpα
  have hreverse := fullTiltedSupportQuarterPair_core_strictAntiOn
    hU hm haffine hρ hρ0 hρK heq hα hτ.2 hphase
      ⟨le_rfl, ht.1.le.trans ht.2.le⟩ (Ioo_subset_Icc_self ht) ht.1
  have hright : (Z t).1 < C := by
    dsimp only at hreverse
    rw [hjoin] at hreverse; exact hreverse.trans hBxα
  have hD0 := (fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow).2.2.1
  have hDorder := (fullTiltedSupportQuarterPair_companion_tangent_order_on_prefix
    hU hm haffine hρ hρ0 hρK heq hτ hcompanion).1
      ⟨le_rfl, hτ.1⟩ ⟨htq.1.le, ht.2.le⟩ htq.1.le
  dsimp only at hDorder
  rw [hD0] at hDorder
  have hDgap : (D t).1 < (Z t).1 := by
    rw [innerCorner_fst_eq_secondTangent (F).f (F).g (F).gD]
    exact lt_add_of_pos_right _ (mul_pos hq hc)
  have hfloor := fullTiltedSupportQuarterPair_first_tangent_nonneg
    hU hm haffine hρ hρ0 hρK heq hheight hunit (Ioo_subset_Icc_self htq)
  have hy : 0 < (Z t).2 := by
    rw [innerCorner_snd_eq_firstTangent (F).f (F).g (F).fD]
    exact sub_pos.mpr ((mul_neg_of_neg_of_pos hp hc).trans_le hfloor)
  have hBgap : (Z t).1 < (B t).1 := by
    rw [innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD]
    exact add_lt_of_neg_right _ (mul_neg_of_neg_of_pos hp hs)
  exact ⟨⟨hDorder.trans_lt hDgap, hright⟩, hy, hBgap, hDgap⟩

/-- Positivity removes the harmless zero clip in the original-to-cut
comparison. Both original walls therefore pass through the literal
two-cap corner at every positive middle contact. -/
theorem fullTiltedSupportQuarterPair_original_walls_core {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) :
    firstWall U t (Z t).1 = (Z t).2 ∧ secondWall U t (Z t).1 = (Z t).2 := by
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hwalls := fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq ht
  refine ⟨hwalls.1, le_antisymm ?_ ?_⟩
  · have h := hU.isCap.secondWall_le_leftCompanionCap ha hb hab haffine hx hs hc
    simpa only [hwalls.2, max_eq_left hy.le] using h
  · rw [← hwalls.2]
    exact secondWall_mono (leftCompanionCap_subset _ _) hU.isCap_fullLeftCompanion.nonempty
      hU.isCap.isCompact hc _

theorem fullTiltedSupportQuarterPair_core_eq_attachedCorner {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) :
    Z t = attachedCorner U t := by
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hcut := (fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq ht).2
  have horiginal := (fullTiltedSupportQuarterPair_original_walls_core
    hU hm haffine hρ hρ0 hρK heq ht hy hx).2
  rw [secondWall, div_eq_iff hc] at hcut horiginal
  have hsupport : support U (companionNormal t) = support V (companionNormal t) := by
    linarith only [hcut, horiginal]
  have hg : angleSupport U (t + Real.pi / 2) = (F).g t := by
    change support U (unitNormal (t + Real.pi / 2)) =
      support V (unitNormal (t + Real.pi / 2))
    simpa only [companionNormal_eq_unitNormal] using hsupport
  apply Prod.ext
  · change (angleSupport U t - 1) * Real.cos t - ((F).g t - 1) * Real.sin t = _
    rw [attachedCorner_fst_eq_support, hg]
  · change (angleSupport U t - 1) * Real.sin t + ((F).g t - 1) * Real.cos t = _
    rw [attachedCorner_snd_eq_support, hg]

/-- The high middle point makes every original companion wall
nonpositive before and at the affine normal. Thus a positive middle
core lies strictly after that normal, not at its omitted atom. -/
theorem fullTiltedSupportQuarterPair_positive_core_after_affine
    (hhigh : capRoof U (horizontalRight U - capWidth U / 4) = 1)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4) : Real.arctan m < t := by
  by_contra hnot
  have hcoef := tilted_initial_coefficient_nonneg ht.1.le (le_of_not_gt hnot)
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hg := hU.isCap.companionSupport_eq_high_of_affine ha hb hab haffine hhigh hs hc.le hcoef
  have hwall : secondWall U t (Z t).1 ≤ 0 := by
    rw [secondWall, companionNormal_eq_unitNormal]
    change (angleSupport U (t + Real.pi / 2) - 1 + (Z t).1 * Real.sin t) / Real.cos t ≤ 0
    rw [hg]
    apply div_nonpos_of_nonpos_of_nonneg _ hc.le
    have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hs
    linarith only [hprod, Real.cos_le_one t]
  rw [(fullTiltedSupportQuarterPair_original_walls_core
    hU hm haffine hρ hρ0 hρK heq ht hy hx).2] at hwall
  exact (not_le_of_gt hy) hwall

theorem fullTiltedSupportQuarterPair_first_wall_lt_core_after
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    {s t : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2)) (ht : t ∈ Ioo 0 (Real.pi / 2))
    (hts : t < s) (hp : p t < 0) :
    firstWall U s (Z t).1 < (Z t).2 := by
  rw [← (fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq ht).1]
  have hB := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  have hd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
      HasDerivAt (fun a => firstWall U a (Z t).1)
        (((Z t).1 - (B r).1) / Real.sin r ^ 2) r := by
    have h := hU.isCap.hasDerivAt_firstWall_of_open_first_density
      hρ hρ0 hρK heq (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hr (Z t).1
    rwa [← fullTiltedSupportQuarterPair_first_tangency
      hU hm haffine hρ hρ0 hρK heq ⟨hr.1.le, hr.2⟩] at h
  apply endpoint_lt_of_hasDerivAt_neg hts
    (fun r hr => hd r ⟨ht.1.trans_le hr.1, hr.2.trans_lt hs.2⟩)
  intro r hr
  have hrq : r ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
  have horder := hB (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self hrq) hr.1.le
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hgap : (Z t).1 < (B t).1 := by
    rw [innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD]
    exact add_lt_of_neg_right _ (mul_neg_of_neg_of_pos hp hsin)
  have hsr : Real.sin r ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hrq.1
    (by linarith only [hrq.2, Real.pi_pos])).ne'
  exact div_neg_of_neg_of_pos (sub_neg.mpr (hgap.trans_le horder))
    (sq_pos_of_ne_zero hsr)

theorem fullTiltedSupportQuarterPair_cut_wall_lt_core_before {τ s t : ℝ}
    (hτ : τ ∈ Icc 0 (Real.pi / 2))
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (hs : s ∈ Ioo 0 (Real.pi / 2)) (ht : t ∈ Ioo 0 τ)
    (hst : s < t) (hq : 0 < q t) :
    secondWall V s (Z t).1 < (Z t).2 := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1, ht.2.trans_le hτ.2⟩
  rw [← (fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq htq).2]
  have hD := (fullTiltedSupportQuarterPair_companion_tangent_order_on_prefix
    hU hm haffine hρ hρ0 hρK heq hτ hunit).1
  apply endpoint_lt_of_hasDerivAt_pos hst
    (fun r hr => fullTiltedSupportQuarterPair_cut_wall_derivative
      hU hm haffine hρ hρ0 hρK heq ⟨hs.1.trans_le hr.1, hr.2.trans_lt htq.2⟩ _)
  intro r hr
  have hrq : r ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hs.1.trans hr.1, hr.2.trans htq.2⟩
  have horder := hD ⟨hrq.1.le, hr.2.le.trans ht.2.le⟩ (Ioo_subset_Icc_self ht) hr.2.le
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], htq.2⟩
  have hgap : (D t).1 < (Z t).1 := by
    rw [innerCorner_fst_eq_secondTangent (F).f (F).g (F).gD]
    exact lt_add_of_pos_right _ (mul_pos hq hc)
  have hcr : Real.cos r ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hrq.1, Real.pi_pos], hrq.2⟩).ne'
  exact div_pos (sub_pos.mpr (horder.trans_lt hgap)) (sq_pos_of_ne_zero hcr)

theorem fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls {t : ℝ}
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hp : p t < 0)
    (hy : 0 < (Z t).2) (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4)
    (hEarlier : ∀ s ∈ Ioo 0 t, secondWall V s (Z t).1 < (Z t).2) :
    sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 ∧
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 s =
          sweptNiche U (Real.pi / 2) (Z t).1 → s = t) := by
  have htq := ht
  have hwalls := fullTiltedSupportQuarterPair_original_walls_core
    hU hm haffine hρ hρ0 hρK heq htq hy hx
  have hcorner : cornerWall U t (Z t).1 = (Z t).2 := by
    rw [cornerWall, hwalls.1, hwalls.2, min_self]
  have hstrict (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hne : s ≠ t) :
      cornerWall U s (Z t).1 < (Z t).2 := by
    rcases lt_or_gt_of_ne hne with hst | hts
    · have hcut := hEarlier s ⟨hs.1, hst⟩
      obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
        (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
      have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le
        (by linarith only [hs.2, Real.pi_pos])
      have hcos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [hs.1, Real.pi_pos], hs.2⟩
      exact (min_le_right _ _).trans_lt
        ((hU.isCap.secondWall_le_leftCompanionCap ha hb hab haffine hx hsin hcos).trans_lt
          (max_lt hcut hy))
    · exact (min_le_left _ _).trans_lt
        (fullTiltedSupportQuarterPair_first_wall_lt_core_after
          hU hm haffine hρ hρ0 hρK heq hunit hs htq hts hp)
  have hN : sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 := by
    apply le_antisymm
    · apply sweptNiche_le_of_forall (by positivity) hy.le
      intro s hs
      by_cases he : s = t
      · simpa only [he] using hcorner.le
      · exact (hstrict s hs he).le
    · rw [← hcorner]
      exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl _) htq
  refine ⟨hN, ?_⟩
  intro s hsc heq
  rw [hN] at heq
  by_contra hne
  by_cases hs0 : s = 0
  · rw [hs0, fullWallClip_zero] at heq
    exact hy.ne' heq.symm
  by_cases hsL : s = Real.pi / 2
  · rw [hsL, fullWallClip_pi_div_two] at heq
    exact hy.ne' heq.symm
  have hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hsc.1 (Ne.symm hs0), lt_of_le_of_ne hsc.2 hsL⟩
  have hmax : fullWallClip hU.isCap.toCompactCap (Z t).1 s < (Z t).2 :=
    max_lt (hstrict s hs hne) hy
  exact (ne_of_lt hmax) heq

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
  apply fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls
    hU hm haffine hρ hρ0 hρK heq hunit ⟨ht.1, ht.2.trans_le hτ.2⟩ hp hy hx
  intro s hs
  exact fullTiltedSupportQuarterPair_cut_wall_lt_core_before hU hm haffine hρ hρ0 hρK heq
    hτ hcompanion ⟨hs.1, hs.2.trans (ht.2.trans_le hτ.2)⟩ ht hs.2 hq

/-- A strict horizontal tangent displacement before the top requires
a strict height loss. This keeps open tangent pieces positive even
when the tangent parameterization contains plateaus. -/
theorem fullTiltedSupportQuarterPair_first_tangent_height_pos_of_abscissa_lt
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Ioo 0 (Real.pi / 2))
    (hst : s ≤ t) (hmove : (B s).1 < (B t).1) : 0 < (B s).2 := by
  obtain ⟨hBx, hBy, _hDx, _hDy, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hsub : uIcc s t ⊆ uIcc (0 : ℝ) (Real.pi / 2) := by
    simpa only [uIcc_of_le hst, uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
      using Icc_subset_Icc hs.1 ht.2.le
  have hmono : MonotoneOn (fun r => -(Real.sin t * (B r).2 + Real.cos t * (B r).1))
      (Icc s t) := by
    apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
      (((hBy.const_mul (Real.sin t)).add (hBx.const_mul (Real.cos t))).neg.mono hsub) hst
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hs.1 ht.2.le) hderiv,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hs.1 ht.2.le) hunit]
      with r hr hdr hur
    have hd := ((hdr.2.1.const_mul (Real.sin t)).add (hdr.1.const_mul (Real.cos t))).neg
    have hformula : -(Real.sin t * ((ρ r - 1) * Real.cos r) +
        Real.cos t * ((1 - ρ r) * Real.sin r)) =
        (1 - ρ r) * Real.sin (t - r) := by
      rw [Real.sin_sub]
      ring
    rw [hformula] at hd
    refine ⟨hd, mul_nonneg (sub_nonneg.mpr hur) ?_⟩
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith only [hr.2]
    · linarith only [hs.1, hr.1, ht.2, Real.pi_pos]
  have horder := hmono (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst
  have hfloor := fullTiltedSupportQuarterPair_first_tangent_nonneg
    hU hm haffine hρ hρ0 hρK heq hheight hunit (Ioo_subset_Icc_self ht)
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
    (by linarith only [ht.2, Real.pi_pos])
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hstrict := mul_pos hcos (sub_pos.mpr hmove)
  have hnonneg := mul_nonneg hsin hfloor
  by_contra hnot
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hsin (le_of_not_gt hnot)
  nlinarith only [horder, hstrict, hnonneg, hnonpos]

/-- At a positive first-tangent contact every maximizing angle has the
same tangent abscissa. The maximizing set may be an angular interval. -/
theorem fullTiltedSupportQuarterPair_first_tangent_abscissa_of_maximizing_angle
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    {s t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (hp : p t ≤ 0) (hy : 0 < (B t).2)
    (hs : s ∈ Icc 0 (Real.pi / 2))
    (hmax : fullWallClip hU.isCap.toCompactCap (B t).1 s =
      sweptNiche U (Real.pi / 2) (B t).1) :
    s ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ (B s).1 = (B t).1 := by
  have hN := fullTiltedSupportQuarterPair_niche_first_tangency
    hU hm haffine hρ hρ0 hρK heq hunit ht hp hy.le
  rw [hN] at hmax
  have hs0 : s ≠ 0 := by
    intro he
    rw [he, fullWallClip_zero] at hmax
    exact hy.ne' hmax.symm
  have hsL : s ≠ Real.pi / 2 := by
    intro he
    rw [he, fullWallClip_pi_div_two] at hmax
    exact hy.ne' hmax.symm
  have hsq : s ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hs.1 hs0.symm, lt_of_le_of_ne hs.2 hsL⟩
  have hvalue : firstWall U s (B t).1 = (B t).2 := by
    have hmin : (B t).2 ≤ cornerWall U s (B t).1 := by
      change max (cornerWall U s (B t).1) 0 = _ at hmax
      rcases max_choice (cornerWall U s (B t).1) 0 with he | he
      · rw [he] at hmax
        exact hmax.ge
      · rw [he] at hmax
        exact False.elim (hy.ne' hmax.symm)
    exact le_antisymm (fullTiltedSupportQuarterPair_first_wall_envelope
      hU hm haffine hρ hρ0 hρK heq hunit ht s hsq) (hmin.trans (min_le_left _ _))
  have hlocal : IsLocalMax (fun r => firstWall U r (B t).1) s := by
    change ∀ᶠ r in 𝓝 s, firstWall U r (B t).1 ≤ firstWall U s (B t).1
    filter_upwards [Ioo_mem_nhds hsq.1 hsq.2] with r hr
    rw [hvalue]
    exact fullTiltedSupportQuarterPair_first_wall_envelope
      hU hm haffine hρ hρ0 hρK heq hunit ht r hr
  have hd := hU.isCap.hasDerivAt_firstWall_of_open_first_density
    hρ hρ0 hρK heq (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hsq (B t).1
  have hz := hlocal.hasDerivAt_eq_zero hd
  rw [← fullTiltedSupportQuarterPair_first_tangency
    hU hm haffine hρ hρ0 hρK heq ⟨hsq.1.le, hsq.2⟩] at hz
  have hsin : Real.sin s ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hsq.1
    (by linarith only [hsq.2, Real.pi_pos])).ne'
  have he := (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 hsin)
  exact ⟨hsq, (sub_eq_zero.mp he).symm⟩

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
  have hmidL : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hmidR : horizontalRight U - capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hsub : Icc s t ⊆ Ioo α τ :=
    fun r hr => ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  have hquarter : Icc s t ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    fun r hr => ⟨hα.trans_lt (hsub hr).1, (hsub hr).2.trans_le hτ.2⟩
  have hgeometry (r : ℝ) (hrI : r ∈ Icc s t) :=
    fullTiltedSupportQuarterPair_core_geometry hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion (hsub hrI)
  have hcontact (r : ℝ) (hr : r ∈ Icc s t) :
      sweptNiche U (Real.pi / 2) (Z r).1 = (Z r).2 ∧
        (∀ a ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap (Z r).1 a =
            sweptNiche U (Real.pi / 2) (Z r).1 → a = r) := by
    apply fullTiltedSupportQuarterPair_core_contact hU hm haffine hρ hρ0 hρK heq hτ
      hunit hcompanion ⟨(hquarter hr).1, (hsub hr).2⟩
      (hphase r (hsub hr)).1 (hphase r (hsub hr)).2 (hgeometry r hr).2.1
    rw [hmidR]
    exact (hgeometry r hr).1.2.le
  have hcont : ContinuousOn (fun r => (Z r).1) (Icc s t) :=
    (fullTiltedSupportQuarterPair_core_continuous hU hm haffine hρ hρ0 hρK heq).1.mono
      (fun r hr => Ioo_subset_Icc_self (hquarter hr))
  have hopen : ∀ x ∈ Ioo (Z t).1 (Z s).1,
      0 < sweptNiche U (Real.pi / 2) x ∧
        (∀ a ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap x a = sweptNiche U (Real.pi / 2) x →
            a ∈ Ioo s t) := by
    intro x hx
    obtain ⟨r, hr, hrx⟩ := intermediate_value_Icc' hst.le hcont (Ioo_subset_Icc_self hx)
    have hN : sweptNiche U (Real.pi / 2) x = (Z r).2 := by
      rw [← hrx]
      exact (hcontact r hr).1
    refine ⟨by rw [hN]; exact (hgeometry r hr).2.1, ?_⟩
    intro a ha hmax
    have hmax' : fullWallClip hU.isCap.toCompactCap (Z r).1 a =
        sweptNiche U (Real.pi / 2) (Z r).1 := by simpa only [hrx] using hmax
    rw [(hcontact r hr).2 a ha hmax']
    constructor
    · apply lt_of_le_of_ne hr.1
      intro he
      have hsr : (Z s).1 = x := by simpa only [← he] using hrx
      exact (ne_of_lt hx.2) hsr.symm
    · apply lt_of_le_of_ne hr.2
      intro he
      have htr : (Z t).1 = x := by simpa only [he] using hrx
      exact (ne_of_lt hx.1) htr
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
  refine ⟨fullTiltedSupportQuarterPair_core_strictAntiOn hU hm haffine hρ hρ0 hρK heq
    hα hτ.2 hphase (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) hst,
    ?_, ?_, (hcontact s hsI).1, (hcontact t htI).1,
    fun x hx => (hopen x hx).1, fun x hx a ha hmax => (hopen x hx).2 a ha hmax⟩
  · rw [hmidL]
    exact (hgeometry t htI).1.1.le
  · rw [hmidR]
    exact (hgeometry s hsI).1.2.le

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
  have hcore := fullTiltedSupportQuarterPair_first_source_core_piece
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hmpos hheight hlow
      hunit hα hτ hpα hphase hcompanion hs ht hst
  have hsub : Icc s t ⊆ Ioo α τ :=
    fun r hrI => ⟨hs.1.trans_le hrI.1, hrI.2.trans_lt ht.2⟩
  have hquarter : Icc s t ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    fun r hrI => ⟨hα.trans_lt (hsub hrI).1, (hsub hrI).2.trans_le hτ.2⟩
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
  have hB := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  have hcontact (r : ℝ) (hrI : r ∈ Icc s t) :
      sweptNiche U (Real.pi / 2) (B r).1 = (B r).2 :=
    fullTiltedSupportQuarterPair_niche_first_tangency hU hm haffine hρ hρ0 hρK heq
      hunit (hquarter hrI) (hphase r (hsub hrI)).1.le
      (fullTiltedSupportQuarterPair_first_tangent_nonneg hU hm haffine hρ hρ0 hρK heq
        hheight hunit (Ioo_subset_Icc_self (hquarter hrI)))
  have hcont : ContinuousOn (fun r => (B r).1) (Icc s t) := by
    have hBx := (fullTiltedSupportQuarterPair_tangent_calculus
      hU hm haffine hρ hρ0 hρK heq).1
    have hclosed : ContinuousOn (fun r => (B r).1) (Icc 0 (Real.pi / 2)) := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)] using hBx.continuousOn
    exact hclosed.mono (fun r hrI => Ioo_subset_Icc_self (hquarter hrI))
  have hopen : ∀ x ∈ Ioo (B s).1 (B t).1,
      0 < sweptNiche U (Real.pi / 2) x ∧
        (∀ a ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap x a = sweptNiche U (Real.pi / 2) x →
            a ∈ Ioo s t) := by
    intro x hx
    obtain ⟨r, hrI, hrx⟩ := intermediate_value_Icc hst.le hcont (Ioo_subset_Icc_self hx)
    have hy : 0 < (B r).2 :=
      fullTiltedSupportQuarterPair_first_tangent_height_pos_of_abscissa_lt
        hU hm haffine hρ hρ0 hρK heq hheight hunit
        (Ioo_subset_Icc_self (hquarter hrI)) (hquarter htI) hrI.2
        (by simpa only [hrx] using hx.2)
    have hN : sweptNiche U (Real.pi / 2) x = (B r).2 := by
      rw [← hrx]
      exact hcontact r hrI
    refine ⟨by rw [hN]; exact hy, ?_⟩
    intro a ha hmax
    have hmax' : fullWallClip hU.isCap.toCompactCap (B r).1 a =
        sweptNiche U (Real.pi / 2) (B r).1 := by simpa only [hrx] using hmax
    have hangle := fullTiltedSupportQuarterPair_first_tangent_abscissa_of_maximizing_angle
      hU hm haffine hρ hρ0 hρK heq hunit (hquarter hrI)
        (hphase r (hsub hrI)).1.le hy ha hmax'
    have hax : (B a).1 = x := hangle.2.trans hrx
    constructor
    · by_contra hnot
      have hle := hB (Ioo_subset_Icc_self hangle.1)
        (Ioo_subset_Icc_self (hquarter hsI)) (le_of_not_gt hnot)
      dsimp only at hle
      rw [hax] at hle
      exact (not_le_of_gt hx.1) hle
    · by_contra hnot
      have hle := hB (Ioo_subset_Icc_self (hquarter htI))
        (Ioo_subset_Icc_self hangle.1) (le_of_not_gt hnot)
      dsimp only at hle
      rw [hax] at hle
      exact (not_le_of_gt hx.2) hle
  refine ⟨hcore, hB (Ioo_subset_Icc_self (hquarter hsI))
    (Ioo_subset_Icc_self (hquarter htI)) hst.le, ?_, ?_,
    hcontact s hsI, hcontact t htI, fun x hx => (hopen x hx).1,
    fun x hx a ha hmax => (hopen x hx).2 a ha hmax⟩
  · exact (fullTiltedSupportQuarterPair_core_geometry hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion hs).2.2.1.le
  · have hright := hB (Ioo_subset_Icc_self (hquarter htI)) hβ htβ
    dsimp only at hright
    rw [hβx] at hright
    have hmidR : horizontalRight U - capWidth U / 4 = C := by
      unfold capWidth
      rw [hl, hr]
      ring
    rw [hmidR]
    exact hright

end ActualPair

end AmbidextrousSofa
