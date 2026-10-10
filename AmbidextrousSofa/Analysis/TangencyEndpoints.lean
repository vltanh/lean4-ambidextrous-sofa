module

public import AmbidextrousSofa.Analysis.HorizontalTopFacet
public import AmbidextrousSofa.Analysis.TangencyLoci

@[expose] public section

/-!
# Actual horizontal top faces and one-sided tangency endpoints

The first inner tangency is the actual right supporting point minus
its unit normal; the second is the same construction in the companion
direction. The true top facet therefore has different left and right
supporting endpoints. One-sided limits below keep that facet and the
two axis faces, rather than replacing the support derivative at an atom.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem firstTangency_eq_vplus_sub_unitNormal (U : Set Plane) (t : ℝ) :
    firstTangency U t = MovingSofaOptimality.vplus U t - unitNormal t := by
  have hframe := MovingSofaOptimality.eq_dot_uvec_smul_add (MovingSofaOptimality.vplus U t) t
  rw [MovingSofaOptimality.dot_vplus_uvec] at hframe
  have hx := congrArg Prod.fst hframe
  have hy := congrArg Prod.snd hframe
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    MovingSofaOptimality.uvec_fst, MovingSofaOptimality.uvec_snd, MovingSofaOptimality.vvec_fst,
    MovingSofaOptimality.vvec_snd] at hx hy
  apply Prod.ext
  · rw [firstTangency_fst_eq_support]
    change (MovingSofaOptimality.supp U t - 1) * Real.cos t -
      MovingSofaOptimality.dot (MovingSofaOptimality.vplus U t) (MovingSofaOptimality.vvec t) * Real.sin t =
        (MovingSofaOptimality.vplus U t).1 - Real.cos t
    nlinarith
  · rw [firstTangency_snd_eq_support]
    change (MovingSofaOptimality.supp U t - 1) * Real.sin t +
      MovingSofaOptimality.dot (MovingSofaOptimality.vplus U t) (MovingSofaOptimality.vvec t) * Real.cos t =
        (MovingSofaOptimality.vplus U t).2 - Real.sin t
    nlinarith

theorem secondTangency_eq_firstTangency_shift (U : Set Plane) (t : ℝ) :
    secondTangency U t = firstTangency U (t + Real.pi / 2) := by
  apply Prod.ext
  · rw [firstTangency_fst_eq_support, secondTangency_fst_eq_support,
      Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    ring
  · rw [firstTangency_snd_eq_support, secondTangency_snd_eq_support,
      Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    ring

theorem secondTangency_eq_vplus_sub_companionNormal (U : Set Plane) (t : ℝ) :
    secondTangency U t = MovingSofaOptimality.vplus U (t + Real.pi / 2) - companionNormal t := by
  rw [secondTangency_eq_firstTangency_shift, firstTangency_eq_vplus_sub_unitNormal,
    companionNormal_eq_unitNormal]

theorem imported_supp_pi_div_two (U : Set Plane) :
    MovingSofaOptimality.supp U (Real.pi / 2) = capHeight U := by
  change support U (unitNormal (Real.pi / 2)) = support U (0, 1)
  simp only [unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem IsFullCapMaximizer.top_vplus_pi_div_two
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    MovingSofaOptimality.vplus U (Real.pi / 2) = (horizontalLeft U + capWidth U / 4, 1) := by
  have hp := MovingSofaOptimality.vplus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)
  have hy : (MovingSofaOptimality.vplus U (Real.pi / 2)).2 = 1 := by
    simpa only [MovingSofaOptimality.suppLine, MovingSofaOptimality.line, Set.mem_ofPred_eq,
      MovingSofaOptimality.dot, MovingSofaOptimality.uvec, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add, imported_supp_pi_div_two, hheight] using hp.2
  have hJ := hU.top_abscissa_mem_middle hheight hmiddle hp.1 hy
  have hw : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  obtain ⟨hl, _, hlr⟩ := hU.isCap.middleChord_endpoints hw
  have hpoint : (horizontalLeft U + capWidth U / 4, 1) ∈ U := by
    simpa only [hmiddle (horizontalLeft U + capWidth U / 4) ⟨le_rfl, hlr.le⟩] using
      capRoof_mem hU.isCap.isCompact hl
  have hedge : (horizontalLeft U + capWidth U / 4, 1) ∈ MovingSofaOptimality.edge U (Real.pi / 2) := by
    refine ⟨hpoint, ?_⟩
    simp only [MovingSofaOptimality.suppLine, MovingSofaOptimality.line, Set.mem_ofPred_eq,
      MovingSofaOptimality.dot, MovingSofaOptimality.uvec, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add, imported_supp_pi_div_two, hheight]
  have hbound := MovingSofaOptimality.dot_le_dot_vplus hU.isCap.isCompact hedge
  simp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi_div_two, Real.cos_pi_div_two,
    mul_neg, mul_one, mul_zero, add_zero] at hbound
  apply Prod.ext _ hy
  change horizontalLeft U + capWidth U / 4 ≤ _ ∧ _ at hJ
  linarith [hJ.1]

theorem IsFullCapMaximizer.top_vminus_pi_div_two
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    MovingSofaOptimality.vminus U (Real.pi / 2) = (horizontalRight U - capWidth U / 4, 1) := by
  have hp := MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)
  have hy : (MovingSofaOptimality.vminus U (Real.pi / 2)).2 = 1 := by
    simpa only [MovingSofaOptimality.suppLine, MovingSofaOptimality.line, Set.mem_ofPred_eq,
      MovingSofaOptimality.dot, MovingSofaOptimality.uvec, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add, imported_supp_pi_div_two, hheight] using hp.2
  have hJ := hU.top_abscissa_mem_middle hheight hmiddle hp.1 hy
  have hw : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  obtain ⟨_, hr, hlr⟩ := hU.isCap.middleChord_endpoints hw
  have hpoint : (horizontalRight U - capWidth U / 4, 1) ∈ U := by
    simpa only [hmiddle (horizontalRight U - capWidth U / 4) ⟨hlr.le, le_rfl⟩] using
      capRoof_mem hU.isCap.isCompact hr
  have hedge : (horizontalRight U - capWidth U / 4, 1) ∈ MovingSofaOptimality.edge U (Real.pi / 2) := by
    refine ⟨hpoint, ?_⟩
    simp only [MovingSofaOptimality.suppLine, MovingSofaOptimality.line, Set.mem_ofPred_eq,
      MovingSofaOptimality.dot, MovingSofaOptimality.uvec, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add, imported_supp_pi_div_two, hheight]
  have hbound := MovingSofaOptimality.dot_vminus_le_dot hU.isCap.isCompact hedge
  simp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi_div_two, Real.cos_pi_div_two,
    mul_neg, mul_one, mul_zero, add_zero] at hbound
  apply Prod.ext _ hy
  change _ ∧ _ ≤ horizontalRight U - capWidth U / 4 at hJ
  linarith [hJ.2]

theorem tendsto_add_const_nhdsGT (a b : ℝ) :
    Tendsto (fun t : ℝ => t + b) (𝓝[>] a) (𝓝[>] (a + b)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨((continuous_id.add_const b).tendsto a).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact add_lt_add_left ht b

theorem tendsto_add_const_nhdsLT (a b : ℝ) :
    Tendsto (fun t : ℝ => t + b) (𝓝[<] a) (𝓝[<] (a + b)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨((continuous_id.add_const b).tendsto a).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact add_lt_add_left ht b

theorem IsDownwardCap.firstTangency_tendsto_zero_right
    {U : Set Plane} (hU : IsDownwardCap U) :
    Tendsto (firstTangency U) (𝓝[>] (0 : ℝ))
      (𝓝 (horizontalRight U - 1, capRoof U (horizontalRight U))) := by
  have hp := MovingSofaOptimality.tendsto_vplus_right hU.imported_isConvexBody 0
  have hn := (continuous_unitNormal.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa only [← firstTangency_eq_vplus_sub_unitNormal, hU.axis_vplus_zero,
    (by simp [unitNormal] : unitNormal 0 = (1, 0)), Prod.mk_sub_mk, sub_zero] using hp.sub hn

theorem IsFullCapMaximizer.secondTangency_tendsto_zero_right
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    Tendsto (secondTangency U) (𝓝[>] (0 : ℝ))
      (𝓝 (horizontalLeft U + capWidth U / 4, 0)) := by
  have hp := (MovingSofaOptimality.tendsto_vplus_right hU.isCap.imported_isConvexBody (Real.pi / 2)).comp
    (by simpa only [zero_add] using tendsto_add_const_nhdsGT 0 (Real.pi / 2))
  have hn := (continuous_companionNormal.tendsto 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa only [Function.comp_apply, ← secondTangency_eq_vplus_sub_companionNormal,
    hU.top_vplus_pi_div_two hheight hmiddle,
    (by simp [companionNormal] : companionNormal 0 = (0, 1)),
    Prod.mk_sub_mk, sub_zero, sub_self] using hp.sub hn

theorem IsFullCapMaximizer.firstTangency_tendsto_pi_div_two_left
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    Tendsto (firstTangency U) (𝓝[<] (Real.pi / 2))
      (𝓝 (horizontalRight U - capWidth U / 4, 0)) := by
  have hp := MovingSofaOptimality.tendsto_vplus_left hU.isCap.imported_isConvexBody (Real.pi / 2)
  have hn := (continuous_unitNormal.tendsto (Real.pi / 2)).mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
  simpa only [← firstTangency_eq_vplus_sub_unitNormal,
    hU.top_vminus_pi_div_two hheight hmiddle,
    (by simp [unitNormal] : unitNormal (Real.pi / 2) = (0, 1)),
    Prod.mk_sub_mk, sub_zero, sub_self] using hp.sub hn

theorem IsDownwardCap.secondTangency_tendsto_pi_div_two_left
    {U : Set Plane} (hU : IsDownwardCap U) :
    Tendsto (secondTangency U) (𝓝[<] (Real.pi / 2))
      (𝓝 (horizontalLeft U + 1, capRoof U (horizontalLeft U))) := by
  have hadd : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
  have hp := (MovingSofaOptimality.tendsto_vplus_left hU.imported_isConvexBody Real.pi).comp
    (by simpa only [hadd] using tendsto_add_const_nhdsLT (Real.pi / 2) (Real.pi / 2))
  have hn := (continuous_companionNormal.tendsto (Real.pi / 2)).mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
  simpa only [Function.comp_apply, ← secondTangency_eq_vplus_sub_companionNormal,
    hU.axis_vminus_pi,
    (by simp [companionNormal] : companionNormal (Real.pi / 2) = (-1, 0)), Prod.mk_sub_mk,
    sub_neg_eq_add, sub_zero] using hp.sub hn

theorem firstCornerVelocity_eq_dot_corner_sub_secondTangency (U : Set Plane) (t : ℝ) :
    firstCornerVelocity U t = coordDot (attachedCorner U t - secondTangency U t) (unitNormal t) := by
  simp only [secondTangency, coordDot, unitNormal, Prod.fst_sub, Prod.snd_sub]
  nlinarith [congrArg (fun z : ℝ => firstCornerVelocity U t * z) (Real.sin_sq_add_cos_sq t)]

theorem secondCornerVelocity_eq_dot_corner_sub_firstTangency (U : Set Plane) (t : ℝ) :
    secondCornerVelocity U t = coordDot (attachedCorner U t - firstTangency U t) (companionNormal t) := by
  simp only [firstTangency, coordDot, companionNormal, Prod.fst_sub, Prod.snd_sub]
  nlinarith [congrArg (fun z : ℝ => secondCornerVelocity U t * z) (Real.sin_sq_add_cos_sq t)]

theorem IsDownwardCap.attachedCorner_zero_of_height_one
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U = 1) :
    attachedCorner U 0 = (horizontalRight U - 1, 0) := by
  apply Prod.ext
  · rw [attachedCorner_fst_eq_support]
    change (MovingSofaOptimality.supp U 0 - 1) * Real.cos 0 -
      (MovingSofaOptimality.supp U (0 + Real.pi / 2) - 1) * Real.sin 0 = _
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero, imported_supp_zero]
  · rw [attachedCorner_snd_eq_support]
    change (MovingSofaOptimality.supp U 0 - 1) * Real.sin 0 +
      (MovingSofaOptimality.supp U (0 + Real.pi / 2) - 1) * Real.cos 0 = _
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add,
      imported_supp_pi_div_two, zero_add, hheight, sub_self]

theorem IsDownwardCap.attachedCorner_pi_div_two_of_height_one
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U = 1) :
    attachedCorner U (Real.pi / 2) = (horizontalLeft U + 1, 0) := by
  have hadd : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
  apply Prod.ext
  · rw [attachedCorner_fst_eq_support]
    change (MovingSofaOptimality.supp U (Real.pi / 2) - 1) * Real.cos (Real.pi / 2) -
      (MovingSofaOptimality.supp U (Real.pi / 2 + Real.pi / 2) - 1) * Real.sin (Real.pi / 2) = _
    rw [hadd, hU.imported_supp_pi]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_sub]
    ring
  · rw [attachedCorner_snd_eq_support]
    change (MovingSofaOptimality.supp U (Real.pi / 2) - 1) * Real.sin (Real.pi / 2) +
      (MovingSofaOptimality.supp U (Real.pi / 2 + Real.pi / 2) - 1) * Real.cos (Real.pi / 2) = _
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, add_zero,
      imported_supp_pi_div_two, hheight, sub_self]

theorem IsFullCapMaximizer.cornerVelocities_tendsto_zero_right
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    Tendsto (fun t => (firstCornerVelocity U t, secondCornerVelocity U t)) (𝓝[>] (0 : ℝ))
      (𝓝 (horizontalRight U - 1 - (horizontalLeft U + capWidth U / 4),
        -capRoof U (horizontalRight U))) := by
  have hC := ((continuous_attachedCorner hU.isCap.isCompact).tendsto 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  rw [hU.isCap.attachedCorner_zero_of_height_one hheight] at hC
  have hD := hU.secondTangency_tendsto_zero_right hheight hmiddle
  have hB := hU.isCap.firstTangency_tendsto_zero_right
  have hn := (continuous_unitNormal.tendsto 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hv := (continuous_companionNormal.tendsto 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hq := ((hC.sub hD).fst_nhds.mul hn.fst_nhds).add ((hC.sub hD).snd_nhds.mul hn.snd_nhds)
  have hr := ((hC.sub hB).fst_nhds.mul hv.fst_nhds).add ((hC.sub hB).snd_nhds.mul hv.snd_nhds)
  change Tendsto (fun t => coordDot (attachedCorner U t - secondTangency U t) (unitNormal t)) _ _ at hq
  change Tendsto (fun t => coordDot (attachedCorner U t - firstTangency U t) (companionNormal t)) _ _ at hr
  simp only [← firstCornerVelocity_eq_dot_corner_sub_secondTangency] at hq
  simp only [← secondCornerVelocity_eq_dot_corner_sub_firstTangency] at hr
  simpa only [unitNormal, companionNormal,
    Real.cos_zero, Real.sin_zero, neg_zero, Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd,
    mul_zero, mul_one, add_zero, zero_add, sub_zero, sub_self, zero_sub] using hq.prodMk_nhds hr

theorem IsFullCapMaximizer.cornerVelocities_tendsto_pi_div_two_left
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    Tendsto (fun t => (firstCornerVelocity U t, secondCornerVelocity U t)) (𝓝[<] (Real.pi / 2))
      (𝓝 (-capRoof U (horizontalLeft U),
        horizontalRight U - capWidth U / 4 - horizontalLeft U - 1)) := by
  have hC := ((continuous_attachedCorner hU.isCap.isCompact).tendsto (Real.pi / 2)).mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
  rw [hU.isCap.attachedCorner_pi_div_two_of_height_one hheight] at hC
  have hD := hU.isCap.secondTangency_tendsto_pi_div_two_left
  have hB := hU.firstTangency_tendsto_pi_div_two_left hheight hmiddle
  have hn := (continuous_unitNormal.tendsto (Real.pi / 2)).mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
  have hv := (continuous_companionNormal.tendsto (Real.pi / 2)).mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
  have hq := ((hC.sub hD).fst_nhds.mul hn.fst_nhds).add ((hC.sub hD).snd_nhds.mul hn.snd_nhds)
  have hr := ((hC.sub hB).fst_nhds.mul hv.fst_nhds).add ((hC.sub hB).snd_nhds.mul hv.snd_nhds)
  change Tendsto (fun t => coordDot (attachedCorner U t - secondTangency U t) (unitNormal t)) _ _ at hq
  change Tendsto (fun t => coordDot (attachedCorner U t - firstTangency U t) (companionNormal t)) _ _ at hr
  simp only [← firstCornerVelocity_eq_dot_corner_sub_secondTangency] at hq
  simp only [← secondCornerVelocity_eq_dot_corner_sub_firstTangency] at hr
  have hfinal := hq.prodMk_nhds hr
  simp only [unitNormal, companionNormal,
    Real.cos_pi_div_two, Real.sin_pi_div_two, Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd,
    mul_zero, mul_one, mul_neg, add_zero, zero_add, sub_zero, sub_self, zero_sub] at hfinal
  convert hfinal using 1 <;> congr 1 <;> ring_nf

end AmbidextrousSofa
