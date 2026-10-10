module

public import AmbidextrousSofa.Analysis.TerminalReflectedParameters
public import AmbidextrousSofa.Analysis.PartialReflectedDynamics

@[expose] public section

/-!
# The actual post-terminal entry into the reflected differential arc

The unused terminal gap is a literal zero-source circle followed by the
single terminal atom. If its first momentum is still positive, its
whole free prefix is positive and yields the exact first-zero quadratic.
The estimate is conditional because that first momentum may already
have crossed zero in the unused gap. No differential equation across
the atom is asserted.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

namespace Analysis

theorem initialFloorCircle_entry_quadratic {d e a : ℝ}
    (hd : 0 ≤ d) (he : e ≤ 1) (ha0 : 0 ≤ a) (haL : a ≤ Real.pi / 2)
    (hqa : 0 < initialFloorCircleQ d (e - 1) a)
    (hpa : 0 < initialFloorCircleP d (e - 1) a) :
    initialFloorCircleP d (e - 1) a ≤ e - d * a + a ^ 2 / 2 ∧
      d - 1 - a ≤ initialFloorCircleQ d (e - 1) a := by
  have hcp : ContDiff ℝ 1 (initialFloorCircleP d (e - 1)) := by
    unfold initialFloorCircleP
    fun_prop
  have hcq : ContDiff ℝ 1 (initialFloorCircleQ d (e - 1)) := by
    unfold initialFloorCircleQ
    fun_prop
  have hqpositive (t : ℝ) (ht : t ∈ Icc 0 a) :
      0 < initialFloorCircleQ d (e - 1) t := by
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi ht.1
      (show a ≤ Real.pi by linarith only [haL, Real.pi_pos]) ht.2
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ t by linarith only [ht.1, Real.pi_pos]) haL ht.2
    have hfirst := mul_nonneg hd (sub_nonneg.mpr hcos)
    have hsecond := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hsin)
    unfold initialFloorCircleQ at *
    nlinarith only [hqa, hfirst, hsecond]
  have hppositive (t : ℝ) (ht : t ∈ Icc 0 a) :
      0 < initialFloorCircleP d (e - 1) t := by
    have hderiv : ∀ᵐ s ∂volume.restrict (Ioo t a),
        HasDerivAt (initialFloorCircleP d (e - 1))
          (-1 - initialFloorCircleQ d (e - 1) s) s ∧
        -1 - initialFloorCircleQ d (e - 1) s ≤ (0 : ℝ) + 0 * (s - t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact ⟨hasDerivAt_initialFloorCircleP _ _ _, by
        linarith only [hqpositive s ⟨ht.1.trans hs.1.le, hs.2.le⟩]⟩
    have h := absolutelyContinuousOnInterval_quadratic_upper_bound
      hcp.contDiffOn.absolutelyContinuousOnInterval ht.2 hderiv
      (show a ∈ Icc t a from ⟨ht.2, le_rfl⟩)
    linarith only [h, hpa]
  have hqbound (t : ℝ) (ht : t ∈ Icc 0 a) :
      d - 1 - t ≤ initialFloorCircleQ d (e - 1) t := by
    have hderiv : ∀ᵐ s ∂volume.restrict (Ioo 0 a),
        HasDerivAt (initialFloorCircleQ d (e - 1))
          (initialFloorCircleP d (e - 1) s - 1) s ∧
        (-1 : ℝ) ≤ initialFloorCircleP d (e - 1) s - 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact ⟨hasDerivAt_initialFloorCircleQ _ _ _, by
        linarith only [hppositive s (Ioo_subset_Icc_self hs)]⟩
    have h := absolutelyContinuousOnInterval_linear_lower_bound
      hcq.contDiffOn.absolutelyContinuousOnInterval ha0 hderiv ht
    have hq0 : initialFloorCircleQ d (e - 1) 0 = d - 1 := by
      simp only [initialFloorCircleQ, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero]
      ring
    rw [hq0] at h
    linarith only [h]
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioo 0 a),
      HasDerivAt (initialFloorCircleP d (e - 1))
        (-1 - initialFloorCircleQ d (e - 1) t) t ∧
      -1 - initialFloorCircleQ d (e - 1) t ≤ -d + (1 : ℝ) * (t - 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ⟨hasDerivAt_initialFloorCircleP _ _ _, by
      linarith only [hqbound t (Ioo_subset_Icc_self ht)]⟩
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound
    hcp.contDiffOn.absolutelyContinuousOnInterval ha0 hderiv
    (show a ∈ Icc 0 a from ⟨ha0, le_rfl⟩)
  have hp0 : initialFloorCircleP d (e - 1) 0 = e := by
    simp only [initialFloorCircleP, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero]
    ring
  rw [hp0] at h
  exact ⟨by nlinarith only [h], hqbound a ⟨ha0, le_rfl⟩⟩

theorem terminal_freeCircle_second_pos {d e α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hd : 3 / 2 < d) (he : 0 ≤ e)
    (hs : 14 / 15 < Real.sin α) (hc : Real.cos α < 3 / 8) :
    0 < initialFloorCircleQ d (e - 1) (Real.pi / 2 - α) := by
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  have hsin : 0 < Real.sin α := by linarith only [hs]
  have hwidth := mul_pos (sub_pos.mpr hd) hsin
  have hheight := mul_nonneg he hcos.le
  simp only [initialFloorCircleQ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  nlinarith only [hwidth, hheight, hs, hc]

end Analysis

theorem IsJointCapMaximizer.properReflected_free_second_pos_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < Analysis.initialFloorCircleQ (terminalReflectedSpan U α)
      (terminalReflectedHeight U α - 1) (Real.pi / 2 - α) := by
  have hparams := hU.centered_terminal_reflected_parameters_of_tail_regime hregime hproper hl hr hheight haffine
  have htrig := terminal_sin_cos_bounds_after_initialAngle
    hU.terminal_angle_gt_arctan_eight_thirds.le hproper
  exact Analysis.terminal_freeCircle_second_pos hU.angle_pos hproper hparams.1 hparams.2.1
    (by linarith only [htrig.1]) (by linarith only [htrig.2])

theorem IsJointCapMaximizer.properReflected_free_second_pos
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < Analysis.initialFloorCircleQ (terminalReflectedSpan U α)
      (terminalReflectedHeight U α - 1) (Real.pi / 2 - α) := by
  exact IsJointCapMaximizer.properReflected_free_second_pos_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine

theorem IsJointCapMaximizer.properReflected_entry_quadratic_of_tail_regime
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t)))
    (hpos : 0 < properReflectedP U m ρ (Real.pi / 2 - α)) :
    properReflectedP U m ρ (Real.pi / 2 - α) ≤ terminalReflectedHeight U α -
      terminalReflectedSpan U α * (Real.pi / 2 - α) + (Real.pi / 2 - α) ^ 2 / 2 ∧
      terminalReflectedSpan U α - 1 - (Real.pi / 2 - α) ≤
        properReflectedQ U m ρ (Real.pi / 2 - α) := by
  have hparams := hU.centered_terminal_reflected_parameters_of_tail_regime hregime hproper hl hr hheight haffine
  have he1 : terminalReflectedHeight U α ≤ 1 := by
    rcases hparams.2.2 with h | h <;> linarith only [h.2.2]
  have htrace := hU.properReflected_terminal_impulse_of_tail_regime hregime hproper hheight haffine hρ hρ0 hρK heq
  have h := Analysis.initialFloorCircle_entry_quadratic
    (show 0 ≤ terminalReflectedSpan U α by linarith only [hparams.1]) he1
    (show 0 ≤ Real.pi / 2 - α by linarith only [hproper])
    (show Real.pi / 2 - α ≤ Real.pi / 2 by linarith only [hU.angle_pos])
    (hU.properReflected_free_second_pos_of_tail_regime hregime hproper hl hr hheight haffine)
    (by rw [← htrace.1]; exact hpos)
  rw [htrace.1, htrace.2]
  exact ⟨h.1, h.2.trans (le_add_of_nonneg_right ENNReal.toReal_nonneg)⟩

theorem IsJointCapMaximizer.properReflected_entry_quadratic
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t)))
    (hpos : 0 < properReflectedP U m ρ (Real.pi / 2 - α)) :
    properReflectedP U m ρ (Real.pi / 2 - α) ≤ terminalReflectedHeight U α -
      terminalReflectedSpan U α * (Real.pi / 2 - α) + (Real.pi / 2 - α) ^ 2 / 2 ∧
      terminalReflectedSpan U α - 1 - (Real.pi / 2 - α) ≤
        properReflectedQ U m ρ (Real.pi / 2 - α) := by
  exact IsJointCapMaximizer.properReflected_entry_quadratic_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine
    hρ hρ0 hρK heq hpos

theorem IsJointCapMaximizer.properReflected_initial_energy_lt_payment_of_tail_regime
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    clippedCornerEnergy (properReflectedP U m ρ) (properReflectedQ U m ρ)
      (Real.pi / 2 - α) < terminalReflectedSpan U α ^ 2 -
        terminalReflectedHeight U α * (1 - terminalReflectedHeight U α) + 1 / 4 + 1 / 30 := by
  have hparams := hU.centered_terminal_reflected_parameters_of_tail_regime hregime hproper hl hr hheight haffine
  have he1 : terminalReflectedHeight U α ≤ 1 := by
    rcases hparams.2.2 with h | h <;> linarith only [h.2.2]
  have hQ := hU.properReflected_free_second_pos_of_tail_regime hregime hproper hl hr hheight haffine
  simp only [Analysis.initialFloorCircleQ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at hQ
  have hmass := hU.terminal_curvature_atom_le_inset_of_tail_regime hregime hproper hheight haffine
  have hpay := Analysis.terminalImpulseEnergyChange_lt_one_thirtieth
    (d := terminalReflectedSpan U α) (e := terminalReflectedHeight U α) hU.angle_pos hproper
    (hU.proper_terminalSlope_lt_three_eighths hproper).le
    (by linarith only [hparams.1]) he1 hmass.1 hmass.2
    (by nlinarith only [hQ])
  have he := hU.properReflected_initial_energy_of_tail_regime hregime hproper hheight haffine hρ hρ0 hρK heq
  have hclip := clippedCornerEnergy_le_initialFloorEnergy
    (properReflectedP U m ρ) (properReflectedQ U m ρ) (Real.pi / 2 - α)
  rw [he] at hclip
  linarith only [hclip, hpay]

theorem IsJointCapMaximizer.properReflected_initial_energy_lt_payment
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    clippedCornerEnergy (properReflectedP U m ρ) (properReflectedQ U m ρ)
      (Real.pi / 2 - α) < terminalReflectedSpan U α ^ 2 -
        terminalReflectedHeight U α * (1 - terminalReflectedHeight U α) + 1 / 4 + 1 / 30 := by
  exact IsJointCapMaximizer.properReflected_initial_energy_lt_payment_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine
    hρ hρ0 hρK heq

theorem IsJointCapMaximizer.properReflected_initial_energy_lt_near_full_payment_of_tail_regime
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) (hκ : terminalSlope α ≤ 1 / 8) :
    clippedCornerEnergy (properReflectedP U m ρ) (properReflectedQ U m ρ)
      (Real.pi / 2 - α) < terminalReflectedSpan U α ^ 2 -
        terminalReflectedHeight U α * (1 - terminalReflectedHeight U α) + 1 / 4 + 1 / 480 := by
  have hparams := hU.centered_terminal_reflected_near_full_parameters_of_tail_regime
    hregime hproper hl hr hheight haffine hκ
  have hQ := hU.properReflected_free_second_pos_of_tail_regime hregime hproper hl hr hheight haffine
  simp only [Analysis.initialFloorCircleQ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at hQ
  have hmass := hU.terminal_curvature_atom_le_inset_of_tail_regime hregime hproper hheight haffine
  have hpay := Analysis.terminalImpulseEnergyChange_lt_one_four_hundred_eightieth
    (d := terminalReflectedSpan U α) (e := terminalReflectedHeight U α)
    hU.angle_pos hproper hκ (by linarith only [hparams.1]) hparams.2.2.2.le
    hmass.1 hmass.2 (by nlinarith only [hQ])
  have he := hU.properReflected_initial_energy_of_tail_regime hregime hproper hheight haffine hρ hρ0 hρK heq
  have hclip := clippedCornerEnergy_le_initialFloorEnergy
    (properReflectedP U m ρ) (properReflectedQ U m ρ) (Real.pi / 2 - α)
  rw [he] at hclip
  linarith only [hclip, hpay]

theorem IsJointCapMaximizer.properReflected_initial_energy_lt_near_full_payment
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) (hκ : terminalSlope α ≤ 1 / 8) :
    clippedCornerEnergy (properReflectedP U m ρ) (properReflectedQ U m ρ)
      (Real.pi / 2 - α) < terminalReflectedSpan U α ^ 2 -
        terminalReflectedHeight U α * (1 - terminalReflectedHeight U α) + 1 / 4 + 1 / 480 := by
  exact IsJointCapMaximizer.properReflected_initial_energy_lt_near_full_payment_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine
    hρ hρ0 hρK heq hκ

end AmbidextrousSofa
