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

theorem Analysis.initialFloorCircle_entry_quadratic {d e a : ℝ}
    (hd : 0 ≤ d) (he : e ≤ 1) (ha0 : 0 ≤ a) (haL : a ≤ Real.pi / 2)
    (hqa : 0 < initialFloorCircleQ d (e - 1) a)
    (hpa : 0 < initialFloorCircleP d (e - 1) a) :
    initialFloorCircleP d (e - 1) a ≤ e - d * a + a ^ 2 / 2 ∧
      d - 1 - a ≤ initialFloorCircleQ d (e - 1) a := by
  have hcp : ContDiff ℝ 1 (initialFloorCircleP d (e - 1)) := by
    unfold initialFloorCircleP; fun_prop
  have hcq : ContDiff ℝ 1 (initialFloorCircleQ d (e - 1)) := by
    unfold initialFloorCircleQ; fun_prop
  have hq (t : ℝ) (ht : t ∈ Icc 0 a) : 0 < initialFloorCircleQ d (e - 1) t := by
    have := mul_nonneg hd (sub_nonneg.mpr
      (Real.cos_le_cos_of_nonneg_of_le_pi ht.1 (by linarith [Real.pi_pos]) ht.2))
    have := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [ht.1, Real.pi_pos]) haL ht.2))
    unfold initialFloorCircleQ at *
    linarith
  have hp (t : ℝ) (ht : t ∈ Icc 0 a) : 0 < initialFloorCircleP d (e - 1) t := by
    have := absolutelyContinuousOnInterval_quadratic_upper_bound (c := 0) (k := 0)
      hcp.contDiffOn.absolutelyContinuousOnInterval ht.2
      (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ⟨hasDerivAt_initialFloorCircleP _ _ _,
        by linarith [hq s ⟨ht.1.trans hs.1.le, hs.2.le⟩]⟩) (right_mem_Icc.mpr ht.2)
    linarith
  have hqb (t : ℝ) (ht : t ∈ Icc 0 a) : d - 1 - t ≤ initialFloorCircleQ d (e - 1) t := by
    have := absolutelyContinuousOnInterval_linear_lower_bound (k := -1)
      hcq.contDiffOn.absolutelyContinuousOnInterval ha0
      (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ⟨hasDerivAt_initialFloorCircleQ _ _ _,
        by linarith [hp s (Ioo_subset_Icc_self hs)]⟩) ht
    simp only [initialFloorCircleQ, Real.cos_zero, Real.sin_zero] at this ⊢
    linarith
  have := absolutelyContinuousOnInterval_quadratic_upper_bound (c := -d) (k := 1)
    hcp.contDiffOn.absolutelyContinuousOnInterval ha0
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ⟨hasDerivAt_initialFloorCircleP _ _ _,
      by linarith [hqb t (Ioo_subset_Icc_self ht)]⟩) (right_mem_Icc.mpr ha0)
  refine ⟨?_, hqb a (right_mem_Icc.mpr ha0)⟩
  simp only [initialFloorCircleP, Real.cos_zero, Real.sin_zero] at this ⊢
  linarith

/-- After the initial angle, the free circle's second momentum `-1 + d sin α - (1 - e) cos α`
at the terminal gap is positive. -/
theorem Analysis.one_lt_terminal_free_second {d e α : ℝ} (hd : 3 / 2 < d) (he : 0 ≤ e)
    (hα : Real.arctan (8 / 3) ≤ α) (hαL : α < Real.pi / 2) :
    1 < d * Real.sin α - (1 - e) * Real.cos α := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_bounds_after_initialAngle hα hαL
  have hcos := Real.cos_pos_of_mem_Ioo ⟨(Real.neg_pi_div_two_lt_arctan _).trans_le hα, hαL⟩
  nlinarith [mul_pos (sub_pos.mpr hd) (by linarith : 0 < Real.sin α), mul_nonneg he hcos.le]

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
  have hparams := hU.centered_terminal_reflected_parameters_of_tail_regime hregime hproper hl hr
    hheight haffine
  have htrace := hU.properReflected_terminal_impulse_of_tail_regime hregime hproper hheight haffine
    hρ hρ0 hρK heq
  have hQ := Analysis.one_lt_terminal_free_second hparams.1 hparams.2.1
    hU.terminal_angle_gt_arctan_eight_thirds.le hproper
  rw [htrace.1] at hpos
  have h := Analysis.initialFloorCircle_entry_quadratic (by linarith [hparams.1])
    (by rcases hparams.2.2 with h | h <;> linarith [h.2.2]) (by linarith) (by linarith [hU.angle_pos])
    (by simp only [Analysis.initialFloorCircleQ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
        linarith) hpos
  rw [htrace.1, htrace.2]
  exact ⟨h.1, h.2.trans (le_add_of_nonneg_right ENNReal.toReal_nonneg)⟩

end AmbidextrousSofa
