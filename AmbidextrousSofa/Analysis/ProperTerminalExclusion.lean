module

public import AmbidextrousSofa.Analysis.ProperExcessEnvelope
public import AmbidextrousSofa.Analysis.TerminalActualComparison
public import AmbidextrousSofa.Analysis.PartialWidthBounds

@[expose] public section

/-!
# Exclusion of an actual largest-angle proper maximizer

The reflected excess envelope is transferred to the literal left-cut
density, with the terminal payment and scalar deadlines of each slope
range. For a near-full terminal angle the entire comparison prefix has
unit density. In the remaining cotangent range the exact cubic payment
is smaller than the terminal margin. The density is constructed inside
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
    {ρ : ℝ → ℝ} {m α θ B : ℝ} (hθ : θ ≤ α)
    (hbound : ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      max (properReflectedFirstDensity m ρ r - 1) 0 ≤
        (19 / 25 : ℝ) * max (B - r) 0) :
    ∀ᵐ t ∂volume.restrict (Icc 0 θ),
      max (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1) 0 ≤
        (19 / 25 : ℝ) * max (t - (Real.pi / 2 - B)) 0 := by
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
  have hleftMiddle : horizontalLeft U + capWidth U / 4 = -C := by rw [hl, hwidth]; ring
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hwidth] at hC
  have hTP := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hregime hproper
    hheight haffine
  -- The early weighted excess of the actual companion is strictly below the terminal margin,
  -- in both terminal-slope ranges.
  have hupper : terminalWeightedExcess (fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2))
      (Real.arcsin (C - topOverhangLeft U)) < (39 / 4400 : ℝ) * Real.cos α := by
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
    -- The reflected excess envelope, with the terminal payment and the scalar deadlines of each
    -- slope range.
    obtain ⟨hd0, he0, hcase⟩ := hU.centered_terminal_reflected_parameters_of_tail_regime hregime
      hproper hl hr hheight haffine
    have hQ := zero_le_one.trans
      (one_lt_terminal_free_second hd0 he0 hU.terminal_angle_gt_arctan_eight_thirds.le hproper).le
    have hmass := hU.terminal_curvature_atom_le_inset_of_tail_regime hregime hproper hheight haffine
    have hexcess := hU.properReflected_ae_excess_bound_of_tail_regime hregime hproper hl hr hheight
      haffine hρ hρ0 hcoarse hκ heq
    by_cases hslope : terminalSlope α ≤ 1 / 8
    · -- Near a full angle the whole comparison prefix has unit density.
      obtain ⟨-, hd1, -, he1⟩ := hU.centered_terminal_reflected_near_full_parameters_of_tail_regime
        hregime hproper hl hr hheight haffine hslope
      have hbound := leftCompanion_excess_bound_of_reflected hθα (hexcess (1 / 480) (73 / 100)
        (43 / 100) (by norm_num) (by norm_num)
        (by linarith only [(terminal_near_full_bounds hU.angle_pos hproper hslope).2.2.1])
        (terminalImpulseEnergyChange_lt_one_four_hundred_eightieth hU.angle_pos hproper hslope
          (by linarith only [hd0]) he1.le hmass.1 hmass.2 hQ)
        (fun hd => (properExcessEnd_lt_near_full hd hd1.le he0 he1.le (by norm_num) le_rfl).le)
        fun hd => (properDecayLength_lt_near_full hd hd1.le he0 (by linarith only [he1]) le_rfl).le)
      rw [terminalWeightedExcess_eq_zero_of_unit_prefix (Real.arcsin_nonneg.mpr hCT.le) ?_]
      · exact mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo
          ⟨by linarith only [hU.angle_pos, Real.pi_pos], hproper⟩)
      filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht hmem
      rw [max_eq_right (show t - (Real.pi / 2 - 73 / 100) ≤ 0 by linarith only [hmem.2, hcut]),
        mul_zero] at ht
      linarith only [ht, le_max_left (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1) 0]
    -- In the remaining cotangent range the cubic payment is below the terminal margin.
    have hd1 : terminalReflectedSpan U α ≤ 2311 / 1000 :=
      hcase.elim (fun h => by linarith only [h.2.1]) fun h => h.2.1.le
    have he1 : terminalReflectedHeight U α ≤ 1 :=
      hcase.elim (fun h => h.2.2.le) fun h => by linarith only [h.2.2]
    exact terminalWeightedExcess_lt_allowance_of_late_tail hCT.le hCT1 hU.angle_pos hproper
      (le_of_not_ge hslope) (terminalWeightedExcess_intervalIntegrable
        (intervalIntegrable_bounded_real_density
          ((measurable_leftCompanionWingDensity hρ m).comp (measurable_id.add_const _))
          (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse _).1)
          (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse _).2) _ _))
      (leftCompanion_excess_bound_of_reflected hθα (hexcess (1 / 30) (91 / 100) (13 / 25)
        (by norm_num) le_rfl (by linarith only [hgap])
        (terminalImpulseEnergyChange_lt_one_thirtieth hU.angle_pos hproper
          (hU.proper_terminalSlope_lt_three_eighths hproper).le (by linarith only [hd0]) he1 hmass.1
          hmass.2 hQ)
        (fun hd => (properExcessEnd_lt_late hd he0 (hcase.imp And.right And.right) (by norm_num)
          le_rfl).le)
        fun hd => (properDecayLength_lt_fifty_two_hundredths hd hd1 he0 he1 le_rfl).le))
  have hinitial := (hU.leftCompanion_actual_initial_data hheight haffine).2.1
  rw [hleftMiddle, hwidth] at hinitial
  have htail := hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime
    hregime hproper hheight haffine
  rw [show horizontalRight U - capWidth U / 4 = C by rw [hr, hwidth]; ring] at htail
  have hcut := hU.proper_leftCompanion_density_of_regular hproper haffine heq
  rw [hleftMiddle] at hcut
  exact hU.false_of_leftCompanion_weighted_excess_of_tail_regime hregime hproper hheight haffine hl hr
    hinitial htail (by linarith [hC.1]) hC.2.le (hU.terminal_cosine_square_cut hproper)
    (topOverhangLeft_nonneg U) (topOverhangRight_nonneg U) hTP
    (measurable_leftCompanionWingDensity hρ m)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse t).1)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse t).2) hcut hupper.le

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
