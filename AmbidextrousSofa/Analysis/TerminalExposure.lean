import AmbidextrousSofa.Analysis.NormalTrimming
import AmbidextrousSofa.Measure.ContactVariation

/-!
# Strict terminal exposure is paid by the actual terminal facet

An inward cut of the actual cap reduces the whole terminal wall by its
vertical displacement and decreases every historical wall. On the strict
terminal exposure this produces a first-order barrier gain. The entire
roof-area loss converges to the horizontal measure of the actual terminal
face. Same-angle maximality therefore bounds strict exposure by that face
width, without a weak source occupation measure or a rule on historical
ties.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem max_sub_max_sub_eq_strictGapRamp {n R ε : ℝ} (hε : 0 ≤ ε) :
    max n R - max n (R - ε) = min ε (max (R - n) 0) := by
  by_cases hRn : R ≤ n
  · rw [max_eq_left hRn, max_eq_left (by linarith : R - ε ≤ n), sub_self,
      max_eq_right (sub_nonpos.mpr hRn), min_eq_right hε]
  · have hnR : n ≤ R := (lt_of_not_ge hRn).le
    rw [max_eq_right hnR, max_eq_left (sub_nonneg.mpr hnR)]
    by_cases hcut : R - ε ≤ n
    · rw [max_eq_left hcut, min_eq_right (by linarith : R - n ≤ ε)]
    · rw [max_eq_right (le_of_not_ge hcut), min_eq_left (by linarith : ε ≤ R - n)]
      ring

theorem firstWall_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 < Real.sin α) (hε : 0 ≤ ε)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α)
    (x : ℝ) : firstWall (normalTrim U α ε) α x = firstWall U α x - ε := by
  unfold firstWall
  rw [support_normalTrim_eq_of_baseline hU hc hs hε hbase]
  field_simp [hs.ne']
  ring

theorem IsDownwardCap.normalTrim_barrier_gain {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2) (hε : 0 ≤ ε)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α)
    (x : ℝ) :
    min ε (max (firstWall U α x - sweptNiche U α x) 0) ≤
      partialBarrier U α x - partialBarrier (normalTrim U α ε) α x := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hV := hU.normalTrim hc hs.le hbase
  have hhistory := sweptNiche_mono (normalTrim_subset U α ε) hV.nonempty
    hU.isCompact hα0 hαL x
  have hN : partialBarrier (normalTrim U α ε) α x ≤
      max (sweptNiche U α x) (firstWall U α x - ε) := by
    unfold partialBarrier
    rw [firstWall_normalTrim hU hc hs hε hbase]
    exact max_le_max hhistory le_rfl
  have h := sub_le_sub_left hN (partialBarrier U α x)
  change max (sweptNiche U α x) (firstWall U α x) -
    max (sweptNiche U α x) (firstWall U α x - ε) ≤ _ at h
  rwa [max_sub_max_sub_eq_strictGapRamp hε] at h

theorem IsDownwardCap.tendsto_integral_terminal_contactRamp
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ} (hs : 0 < Real.sin α) :
    Tendsto (fun ε : ℝ => ∫ x in Icc (horizontalLeft U) (horizontalRight U),
      max (ε - (outerSupportingRoof U α x - capRoof U x)) 0 / ε) (𝓝[>] 0)
      (𝓝 (terminalFaceWidth U α)) := by
  let I := Icc (horizontalLeft U) (horizontalRight U)
  let d : ℝ → ℝ := fun x => outerSupportingRoof U α x - capRoof U x
  have hd : Measurable d := (continuous_outerSupportingRoof U α).measurable.sub
    hU.measurable_capRoof
  have hd0 : ∀ᵐ x ∂volume.restrict I, 0 ≤ d x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply sub_nonneg.mpr
    apply hU.capRoof_le_outerSupportingRoof hs
    rwa [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  have hlim := tendsto_integral_contactRamp_quotient (volume.restrict I) hd hd0
  have hset : {x | d x = 0} ∩ I = horizontalProjection (Imported.edge U α) := by
    rw [inter_comm]
    change {x ∈ I | outerSupportingRoof U α x - capRoof U x = 0} = _
    rw [show I = horizontalProjection U from
      (horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex).symm]
    exact hU.outerSupportingRoof_contact hs
  have hmeasure : (volume.restrict I).real {x | d x = 0} = terminalFaceWidth U α := by
    rw [measureReal_restrict_apply (measurableSet_eq_fun hd measurable_const), hset,
      ← hU.terminalFaceWidth_eq_projection_measure hs.le]
  rw [hmeasure] at hlim
  exact hlim

theorem IsDownwardCap.tendsto_integral_terminal_strictGapRamp
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ}
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    Tendsto (fun ε : ℝ => ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      min ε (max (firstWall U α x - sweptNiche U α x) 0) / ε) (𝓝[>] 0)
      (𝓝 (volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        terminalStrictRegion U α))) := by
  let J := middleHalfInterval (horizontalLeft U) (horizontalRight U)
  let d : ℝ → ℝ := fun x => firstWall U α x - sweptNiche U α x
  have hd : Measurable d := (continuous_firstWall U α).measurable.sub
    (measurable_sweptNiche hU.isCompact (by linarith [Real.pi_pos]) hαL)
  have hlim := tendsto_integral_strictGapRamp_quotient (volume.restrict J) hd
  have hset : {x | 0 < d x} ∩ J = J ∩ terminalStrictRegion U α := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, terminalStrictRegion, d, sub_pos]
    exact and_comm
  have hmeasure : (volume.restrict J).real {x | 0 < d x} =
      volume.real (J ∩ terminalStrictRegion U α) := by
    rw [measureReal_restrict_apply (measurableSet_lt measurable_const hd), hset]
  rw [hmeasure] at hlim
  exact hlim

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
  let V := normalTrim U α ε
  let I := Icc (horizontalLeft U) (horizontalRight U)
  let J := middleHalfInterval (horizontalLeft U) (horizontalRight U)
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [hU.angle_mem.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hU.angle_pos, Real.pi_pos], hU.angle_mem.2⟩
  have hV : IsDownwardCap V := hU.isCap.normalTrim hc hs.le hbase
  have hleft := horizontalLeft_normalTrim hU.isCap hc hbase
  have hright := horizontalRight_normalTrim hU.isCap hc hbase
  have hAI : IntegrableOn (capRoof U) I :=
    hU.isCap.integrableOn_capRoof_Icc _ _
  have hAVI : IntegrableOn (capRoof V) I := hV.integrableOn_capRoof_Icc _ _
  have hAext := hAI.mono_set (show I \ J ⊆ I from diff_subset)
  have hAVext := hAVI.mono_set (show I \ J ⊆ I from diff_subset)
  have hNU : IntegrableOn (partialBarrier U α) J :=
    integrableOn_partialBarrier_Icc hU.isCap.isCompact hU.angle_pos hU.angle_mem.2 _ _
  have hNV : IntegrableOn (partialBarrier V α) J :=
    integrableOn_partialBarrier_Icc hV.isCompact hU.angle_pos hU.angle_mem.2 _ _
  have hBcont : Continuous (fun x => min ε (max (firstWall U α x - sweptNiche U α x) 0)) :=
    continuous_const.min (((continuous_firstWall U α).sub
      (hU.isCap.continuous_sweptNiche_terminalAngle hU.angle_mem)).max continuous_const)
  have hBint : IntegrableOn (fun x => min ε (max (firstWall U α x - sweptNiche U α x) 0)) J :=
    hBcont.integrableOn_Icc
  have hgain :
      (∫ x in J, min ε (max (firstWall U α x - sweptNiche U α x) 0)) ≤
        (∫ x in J, partialBarrier U α x) - ∫ x in J, partialBarrier V α x := by
    rw [← integral_sub hNU hNV]
    exact integral_mono hBint (hNU.sub hNV)
      (fun x => hU.isCap.normalTrim_barrier_gain hU.angle_pos hU.angle_mem.2 hε hbase x)
  have hloss : (∫ x in I \ J, capRoof U x) - (∫ x in I \ J, capRoof V x) ≤
      ∫ x in I, max (ε - (outerSupportingRoof U α x - capRoof U x)) 0 := by
    rw [← integral_sub hAext hAVext]
    calc
      (∫ x in I \ J, capRoof U x - capRoof V x) ≤
          ∫ x in I, capRoof U x - capRoof V x :=
        setIntegral_mono_set (hAI.sub hAVI)
          (Eventually.of_forall (fun x => sub_nonneg.mpr
            (hV.capRoof_mono hU.isCap (normalTrim_subset U α ε) x)))
          (Eventually.of_forall (fun x hx => hx.1))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact capRoof_sub_normalTrim hU.isCap hc hs hbase
          ((horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex).symm ▸ hx)
  have hscore := hU.score_le_same_angle hV
  rw [capScore_eq_integrals, capScore_eq_integrals, hleft, hright] at hscore
  change (∫ x in I \ J, capRoof V x) - (∫ x in J, partialBarrier V α x) ≤
    (∫ x in I \ J, capRoof U x) - ∫ x in J, partialBarrier U α x at hscore
  linarith only [hgain, hloss, hscore]

theorem IsJointCapMaximizer.terminal_strict_exposure_measure_le_faceWidth_of_baseline
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (hbase : horizontalRight U * Real.cos α < support U (unitNormal α)) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      terminalStrictRegion U α) ≤ terminalFaceWidth U α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [Real.pi_pos])
  let δ := (support U (unitNormal α) - horizontalRight U * Real.cos α) / Real.sin α
  have hδ : 0 < δ := div_pos (sub_pos.mpr hbase) hs
  apply le_of_tendsto_of_tendsto
    (hU.isCap.tendsto_integral_terminal_strictGapRamp hU.angle_mem.1 hαL.le)
    (hU.isCap.tendsto_integral_terminal_contactRamp hs)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hbaseε : horizontalRight U * Real.cos α ≤
      support U (unitNormal α) - ε * Real.sin α := by
    have h := (le_div_iff₀ hs).mp hε.2.le
    linarith only [h]
  have h := div_le_div_of_nonneg_right
    (hU.integral_strictGapRamp_le_contactRamp hε.1.le hbaseε) hε.1.le
  simpa only [integral_div] using h

/-- This is an actual cap-variation consequence at the selected canonical
maximizer. Historical ties remain unrestricted. -/
theorem IsJointCapMaximizer.terminal_strict_exposure_measure_le_faceWidth_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      terminalStrictRegion U α) ≤ terminalFaceWidth U α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [Real.pi_pos])
  exact hU.terminal_strict_exposure_measure_le_faceWidth_of_baseline hαL
    (hU.isCap.support_right_baseline_strict hs (hs.trans_le
      (hU.terminal_vminus_height_ge_sin_of_tail_regime hregime hαL hheight haffine)))

theorem IsJointCapMaximizer.terminal_strict_exposure_measure_le_faceWidth
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      terminalStrictRegion U α) ≤ terminalFaceWidth U α := by
  exact IsJointCapMaximizer.terminal_strict_exposure_measure_le_faceWidth_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

theorem IsJointCapMaximizer.terminal_strict_exposure_measure_le_reserve_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      terminalStrictRegion U α) ≤ terminalTailReserve U α :=
  (hU.terminal_strict_exposure_measure_le_faceWidth_of_tail_regime hregime hαL hheight haffine).trans
    (hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hαL hheight haffine)

theorem IsJointCapMaximizer.terminal_strict_exposure_measure_le_reserve
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      terminalStrictRegion U α) ≤ terminalTailReserve U α := by
  exact IsJointCapMaximizer.terminal_strict_exposure_measure_le_reserve_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

end AmbidextrousSofa
