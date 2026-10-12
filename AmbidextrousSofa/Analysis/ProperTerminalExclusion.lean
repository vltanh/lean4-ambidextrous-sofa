module

public import AmbidextrousSofa.Analysis.ProperExcessEnvelope
public import AmbidextrousSofa.Analysis.TerminalActualComparison
public import AmbidextrousSofa.Analysis.PartialWidthBounds

@[expose] public section

/-!
# Exclusion of an actual largest-angle proper maximizer

The reflected excess envelope is transferred to the literal left-cut
density, with one geometric impulse payment and a deadline proportional to
terminal slope. The cubic overlap payment is smaller than the terminal
margin throughout the slope range. The density is constructed inside
the exclusion theorem from the actual selected-source limit.

Centering, height normalization and middle-chord replacement preserve
the maximizing angle, so the exclusion applies to the genuine
largest-angle maximum. This reduces the global cap-and-angle objective
to the full-angle cap objective, without assuming its sharp value.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

open Analysis

theorem leftCompanion_excess_bound_of_reflected
    {ρ : ℝ → ℝ} {m α θ B K : ℝ} (hθ : θ ≤ α)
    (hbound : ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      max (properReflectedFirstDensity m ρ r - 1) 0 ≤
        K * max (B - r) 0) :
    ∀ᵐ t ∂volume.restrict (Icc 0 θ),
      max (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1) 0 ≤
        K * max (t - (Real.pi / 2 - B)) 0 := by
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioo).mp hbound)
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with t ht hs
  simpa only [properReflectedFirstDensity, sub_sub_cancel,
    show B - (Real.pi / 2 - t) = t - (Real.pi / 2 - B) by ring] using
    hs ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- Every density and endpoint input in the contradiction is produced
from the same actual maximizing cap. -/
theorem IsJointCapMaximizer.false_of_centered_proper_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : False := by
  obtain ⟨ρ, hρ, hsharp, hcoarse, heq⟩ :=
    hU.curvature_density_on_regular_proper_domain hproper haffine
  obtain ⟨hρ0, hκ⟩ := forall_and.mp hsharp
  have hwidth : capWidth U / 4 = C := by unfold capWidth; rw [hl, hr]; ring
  have hleftMiddle : horizontalLeft U + capWidth U / 4 = -C := (centered_quarter_points hl hr).1
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hwidth] at hC
  have hTP := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hregime hproper
    hheight haffine
  -- The early weighted excess of the actual companion is strictly below the terminal margin,
  -- using the same angular budget throughout the terminal-slope range.
  have hupper : terminalWeightedExcess (fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2))
      (Real.arcsin (C - topOverhangLeft U)) < terminalCircleGap * Real.cos α := by
    have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
    have hCT : 0 < C - topOverhangLeft U := by
      linarith [hC.1, topOverhangRight_nonneg U, (hU.isCap.terminalTailInset_bounds hU.angle_pos
        hproper hH).2.1, (terminal_sin_cos_bounds_after_initialAngle
        hU.terminal_angle_gt_arctan_eight_thirds.le hproper).2]
    have hCT1 : C - topOverhangLeft U ≤ 37 / 50 := by linarith [hC.2, topOverhangLeft_nonneg U]
    have hcut := eleven_fifteenths_lt_arccos_of_le (by linarith) hCT1
    rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hcut
    have hgap : Real.pi / 2 - α < 3 / 8 := by
      rw [terminal_gap_eq_arctan_slope hU.angle_pos hproper]
      exact (Real.arctan_lt_self (terminalSlope_pos hU.angle_pos hproper)).trans
        (hU.proper_terminalSlope_lt_three_eighths hproper)
    have hθα : Real.arcsin (C - topOverhangLeft U) ≤ α := by linarith
    obtain ⟨hd0, hdSlope, he0, he1, hbudget⟩ :=
      hU.centered_terminal_reflected_angular_budget_of_tail_regime hregime hproper hl hr hheight haffine
    have hslope := hU.proper_terminalSlope_lt_three_eighths hproper
    have hslope0 := terminalSlope_pos hU.angle_pos hproper
    have hd1 : terminalReflectedSpan U α ≤ properBaselineSpan + (3 / 8) / 4 := by
      linarith only [hdSlope, hslope]
    have hQ := zero_le_one.trans
      (one_lt_terminal_free_second hd0 he0 hU.terminal_angle_gt_arctan_eight_thirds.le hproper).le
    have hmass := hU.terminal_curvature_atom_le_inset_of_tail_regime hregime hproper hheight haffine
    have hinset := terminalInset_le_half_slope hU.angle_pos hproper
    have hηSlope : terminalInset α ^ 2 ≤ terminalSlope α ^ 2 / 4 := by
      nlinarith only [pow_le_pow_left₀ (terminalInset_pos hU.angle_pos hproper).le hinset 2]
    have hηMax : terminalInset α ^ 2 ≤ (3 / 8 : ℝ) ^ 2 / 4 := by
      linarith only [hηSlope, pow_le_pow_left₀ hslope0.le hslope.le 2]
    have hgapSlope : Real.pi / 2 - α < terminalSlope α := by
      rw [terminal_gap_eq_arctan_slope hU.angle_pos hproper]
      exact Real.arctan_lt_self hslope0
    have hdeadline := hU.properReflected_ae_excess_bound_of_tail_regime hregime hproper hl hr hheight
      haffine hρ hρ0 hcoarse hκ heq (terminalInset α ^ 2) (properAngularDeadline (terminalSlope α))
      (3 / 5) (sq_nonneg _) hηMax (by norm_num) (by norm_num)
      (by dsimp [properAngularDeadline]; linarith only [hgapSlope, hslope])
      (terminalImpulseEnergyChange_lt_inset_sq hU.angle_pos hproper (by linarith only [hd0])
        he1 hmass.1 hmass.2 hQ)
      (fun hd => properExcessEnd_le_angular_deadline hslope0.le hslope.le hd hd1 he0 he1
        (sq_nonneg _) hηMax hηSlope hbudget)
      (fun hd => (properDecayLength_lt_three_fifths hd hd1 he0 he1 hηMax).le)
    norm_num only at hdeadline
    exact terminalWeightedExcess_lt_allowance_of_angular_budget hCT.le hCT1 hU.angle_pos hproper hslope.le
      (terminalWeightedExcess_intervalIntegrable
        (intervalIntegrable_bounded_real_density
          ((measurable_leftCompanionWingDensity hρ m).comp (measurable_id.add_const _))
          (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse _).1)
          (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse _).2) _ _))
      (leftCompanion_excess_bound_of_reflected hθα hdeadline)

  have hinitial := (hU.leftCompanion_actual_initial_data hheight haffine).2.1
  rw [hleftMiddle, hwidth] at hinitial
  have htail := hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime
    hregime hproper hheight haffine
  rw [show horizontalRight U - capWidth U / 4 = C from (centered_quarter_points hl hr).2.1] at htail
  have hcut := hU.proper_leftCompanion_density_of_regular hproper haffine heq
  rw [hleftMiddle] at hcut
  exact hU.false_of_leftCompanion_weighted_excess_of_tail_regime hregime hproper hheight haffine hl hr
    hinitial htail (by linarith [hC.1]) hC.2.le (hU.terminal_cosine_square_cut hproper)
    (topOverhangLeft_nonneg U) (topOverhangRight_nonneg U) hTP
    (measurable_leftCompanionWingDensity hρ m)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse t).1)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse t).2) hcut hupper

theorem IsJointCapMaximizer.angle_eq_pi_div_two_of_largest
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α) :
    α = Real.pi / 2 := by
  refine le_antisymm hU.angle_mem.2 (not_lt.mp fun hproper => ?_)
  obtain ⟨V, hV, hl, hr, hheight, m, c, haffine⟩ := hU.exists_centered_heightOne_affine
  exact hV.false_of_centered_proper_tail_regime
    (hV.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine

theorem exists_jointCapMaximizer_full_angle :
    ∃ U : Set Plane, IsJointCapMaximizer U (Real.pi / 2) := by
  obtain ⟨U, α, hU, _, hLargest⟩ := exists_jointCapMaximizer_largest_angle
  exact ⟨U, hU.angle_eq_pi_div_two_of_largest hLargest ▸ hU⟩

/-- A full-angle maximum now also maximizes over all allowed terminal
angles. Its sharp score is a separate full-cap theorem. -/
theorem IsFullCapMaximizer.isJointCapMaximizer
    {U : Set Plane} (hU : IsFullCapMaximizer U) : IsJointCapMaximizer U (Real.pi / 2) := by
  obtain ⟨V, hV⟩ := exists_jointCapMaximizer_full_angle
  exact hV.of_score_le hU.isCap ⟨by linarith [Real.pi_pos], le_rfl⟩ (hU.2 V hV.isCap)

end AmbidextrousSofa
