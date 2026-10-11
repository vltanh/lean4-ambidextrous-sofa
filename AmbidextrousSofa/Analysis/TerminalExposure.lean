module

public import AmbidextrousSofa.Analysis.NormalTrimming
public import AmbidextrousSofa.Measure.ContactVariation

@[expose] public section

/-!
# Strict terminal exposure is paid by the actual terminal facet

An inward cut of the actual cap reduces the whole terminal wall by its
vertical displacement and decreases every historical wall. On the strict
terminal exposure this produces a first-order barrier gain. The entire
roof-area loss converges to the horizontal measure of the actual terminal
face. Same-angle maximality therefore bounds strict exposure by that face
width.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.tendsto_integral_terminal_contactRamp
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ} (hs : 0 < Real.sin α) :
    Tendsto (fun ε : ℝ => ∫ x in Icc (horizontalLeft U) (horizontalRight U),
      max (ε - (outerSupportingRoof U α x - capRoof U x)) 0 / ε) (𝓝[>] 0)
      (𝓝 (terminalFaceWidth U α)) := by
  have hP := horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex
  have hd : Measurable fun x => outerSupportingRoof U α x - capRoof U x :=
    (continuous_outerSupportingRoof U α).measurable.sub hU.measurable_capRoof
  convert tendsto_integral_contactRamp_quotient _ hd (ae_restrict_of_forall_mem measurableSet_Icc
    fun x hx => sub_nonneg.mpr (hU.capRoof_le_outerSupportingRoof hs (hP ▸ hx))) using 2
  · rw [measureReal_restrict_apply (measurableSet_eq_fun hd measurable_const),
      hU.terminalFaceWidth_eq_projection_measure hs.le, ← hU.outerSupportingRoof_contact hs, hP,
      inter_comm]
    rfl
  · infer_instance

theorem IsDownwardCap.tendsto_integral_terminal_strictGapRamp
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ}
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    Tendsto (fun ε : ℝ => ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      min ε (max (firstWall U α x - sweptNiche U α x) 0) / ε) (𝓝[>] 0)
      (𝓝 (volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        terminalStrictRegion U α))) := by
  have hd : Measurable fun x => firstWall U α x - sweptNiche U α x :=
    (continuous_firstWall U α).measurable.sub
      (measurable_sweptNiche hU.isCompact (by linarith [Real.pi_pos]) hαL)
  convert tendsto_integral_strictGapRamp_quotient _ hd using 2
  · rw [measureReal_restrict_apply (measurableSet_lt measurable_const hd), inter_comm]
    simp only [terminalStrictRegion, sub_pos]
  · unfold middleHalfInterval; infer_instance

/-- Same-angle maximality compares the literal barrier gain with the
whole roof-area loss. Using the whole roof only enlarges the loss bound. -/
theorem IsJointCapMaximizer.integral_strictGapRamp_le_contactRamp
    {U : Set Plane} {α ε : ℝ} (hU : IsJointCapMaximizer U α)
    (hε : 0 ≤ ε)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      min ε (max (firstWall U α x - sweptNiche U α x) 0)) ≤
    ∫ x in Icc (horizontalLeft U) (horizontalRight U),
      max (ε - (outerSupportingRoof U α x - capRoof U x)) 0 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [hU.angle_mem.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hU.angle_pos, Real.pi_pos], hU.angle_mem.2⟩
  have hV := hU.isCap.normalTrim hc hs.le hbase
  have hscore := hU.score_le_same_angle hV
  rw [capScore_eq_integrals, capScore_eq_integrals, horizontalLeft_normalTrim hU.isCap hc hbase,
    horizontalRight_normalTrim hU.isCap hc hbase] at hscore
  set V := normalTrim U α ε
  set I := Icc (horizontalLeft U) (horizontalRight U)
  set J := middleHalfInterval (horizontalLeft U) (horizontalRight U)
  have hAI : IntegrableOn (capRoof U) I := hU.isCap.integrableOn_capRoof_Icc _ _
  have hAVI : IntegrableOn (capRoof V) I := hV.integrableOn_capRoof_Icc _ _
  have hNU : IntegrableOn (partialBarrier U α) J :=
    integrableOn_partialBarrier_Icc hU.isCap.isCompact hU.angle_pos hU.angle_mem.2 _ _
  have hNV : IntegrableOn (partialBarrier V α) J :=
    integrableOn_partialBarrier_Icc hV.isCompact hU.angle_pos hU.angle_mem.2 _ _
  have hgain : (∫ x in J, min ε (max (firstWall U α x - sweptNiche U α x) 0)) ≤
      (∫ x in J, partialBarrier U α x) - ∫ x in J, partialBarrier V α x := by
    rw [← integral_sub hNU hNV]
    refine integral_mono_of_nonneg (.of_forall fun x => le_min hε (le_max_right _ _)) (hNU.sub hNV)
      (.of_forall fun x => ?_)
    -- The cut lowers the terminal wall by `ε` and does not raise the historical walls.
    have hN : sweptNiche V α x ≤ sweptNiche U α x := sweptNiche_mono (normalTrim_subset U α ε)
      hV.nonempty hU.isCap.isCompact hU.angle_pos hU.angle_mem.2 x
    have hW : firstWall V α x = firstWall U α x - ε := by
      simp only [V, firstWall, support_normalTrim_eq_of_baseline hU.isCap hc hs hε hbase]
      field_simp
      ring
    simp only [partialBarrier, hW, min_def, max_def]
    split_ifs <;> linarith
  have hloss : (∫ x in I \ J, capRoof U x) - (∫ x in I \ J, capRoof V x) ≤
      ∫ x in I, max (ε - (outerSupportingRoof U α x - capRoof U x)) 0 := by
    rw [← integral_sub (hAI.mono_set sdiff_subset) (hAVI.mono_set sdiff_subset),
      ← setIntegral_congr_fun measurableSet_Icc fun x hx => capRoof_sub_normalTrim hU.isCap hc hs
        hbase ((horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact
          hU.isCap.convex).symm ▸ hx)]
    exact setIntegral_mono_set (hAI.sub hAVI) (.of_forall fun x => sub_nonneg.mpr
      (hV.capRoof_mono hU.isCap (normalTrim_subset U α ε) x)) (.of_forall fun x hx => hx.1)
  linarith only [hgain, hloss, hscore]

/-- In the proper tail regime, strict terminal exposure on the middle window is at most the
reserve. -/
theorem IsJointCapMaximizer.terminal_strict_exposure_measure_le_reserve_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      terminalStrictRegion U α) ≤ terminalTailReserve U α := by
  have hs := (terminal_sin_cos_pos hU.angle_pos hαL).1
  have hbase := hU.isCap.support_right_baseline_strict hs
    (hs.trans_le (hU.terminal_vminus_height_ge_sin_of_tail_regime hregime hαL hheight haffine))
  refine (le_of_tendsto_of_tendsto
    (hU.isCap.tendsto_integral_terminal_strictGapRamp hU.angle_mem.1 hαL.le)
    (hU.isCap.tendsto_integral_terminal_contactRamp hs) ?_).trans
    (hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hαL hheight haffine)
  filter_upwards [Ioo_mem_nhdsGT (div_pos (sub_pos.mpr hbase) hs)] with ε ⟨hε, hεδ⟩
  rw [lt_div_iff₀ hs] at hεδ
  rw [integral_div, integral_div]
  exact div_le_div_of_nonneg_right (hU.integral_strictGapRamp_le_contactRamp hε.le
    (by linarith)) hε.le

end AmbidextrousSofa
