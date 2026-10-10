import AmbidextrousSofa.Analysis.TerminalCompanionCurvature
import AmbidextrousSofa.Analysis.TerminalCircleMargin

/-!
# The actual companion-wall circle comparison

The literal curvature measure determines both companion-coordinate
moments. The actual supporting point at a localized positive wall
maximum then supplies the horizontal moment and the wall height. This
proves the weighted circle estimate for the whole visited niche.

The density equality is an explicit input. Its proper-cap construction,
the positive-tilt charged-wing reduction, and the early excess estimate
remain separate obligations; no cap-score or occupation certificate is
assumed by these geometric and analytic bridges.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- Every actual companion wall is bounded using only the early
weighted excess. The cap itself supplies both initial coordinates. -/
theorem IsDownwardCap.max_secondWall_le_circle_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ}
    {K α x r : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hA : 0 < companionInitialOffset U)
    (hAB : companionInitialOffset U ≤ x - horizontalLeft U)
    (hBα : x - horizontalLeft U < Real.sin α)
    (hsub : Ioc (Real.pi / 2)
      (Real.arcsin (x - horizontalLeft U) + Real.pi / 2) ⊆ S)
    (hr : r ∈ Icc 0 α) :
    max (secondWall U r x) 0 ≤
      circleHeight (companionInitialOffset U) - circleHeight (x - horizontalLeft U) +
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
          (Real.arcsin (companionInitialOffset U)) := by
  have hB0 : 0 ≤ x - horizontalLeft U := hA.le.trans hAB
  have hB1 : x - horizontalLeft U < 1 := hBα.trans_le (Real.sin_le_one α)
  have hv : IntervalIntegrable (fun t => ρ (t + Real.pi / 2)) volume 0
      (Real.arcsin (x - horizontalLeft U)) :=
    intervalIntegrable_bounded_real_density (hρ.comp (measurable_id.add_const _))
      (fun t => hρ0 _) (fun t => hρK _) _ _
  have hv0 : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.arcsin (x - horizontalLeft U))),
      0 ≤ ρ (t + Real.pi / 2) := Eventually.of_forall (fun t => hρ0 _)
  by_cases hpositive : ∃ t ∈ Icc 0 α, 0 < secondWall U t x
  · obtain ⟨t, ht, htB, _htpositive, hmax, hcontactX, hcontactY⟩ :=
      hU.exists_positive_localized_secondWall_max hα0 hαL hB0 hBα le_rfl hpositive
    have hmom := hU.shiftedCompanion_eq_initial_add_integral_of_density
      hρ hρ0 hρK heq ht.1.le
      ((Ioc_subset_Ioc le_rfl (add_le_add_right htB _)).trans hsub)
    have hX : shiftedCompanionX U t = x := hcontactX
    have hY : secondWall U t x = shiftedCompanionY U t := hcontactY
    have hhorizontal : (∫ q in 0..t, (1 - ρ (q + Real.pi / 2)) * Real.cos q) =
        (x - horizontalLeft U) - companionInitialOffset U := by
      rw [hX] at hmom
      linarith only [hmom.1]
    have hvertical : secondWall U t x + companionInitialDeficit U =
        ∫ q in 0..t, (1 - ρ (q + Real.pi / 2)) * Real.sin q := by
      rw [hY]
      exact hmom.2
    have hbound := terminal_weighted_companion_height_bound hA hAB hB1 ht.1.le htB hv hv0
      hhorizontal hU.companionInitialDeficit_nonneg hvertical
    exact (max_le_max (hmax hr) le_rfl).trans hbound
  · have hwall : secondWall U r x ≤ 0 := le_of_not_gt
      (fun h => hpositive ⟨r, hr, h⟩)
    rw [max_eq_right hwall]
    have hcircle := circleHeight_antitoneOn ⟨hA, hAB.trans_lt hB1⟩
      ⟨hA.trans_le hAB, hB1⟩ hAB
    have hexcess := terminalWeightedExcess_nonneg
      (v := fun t => ρ (t + Real.pi / 2)) (Real.arcsin_nonneg.mpr hA.le)
      (Real.arcsin_lt_pi_div_two.mpr (hAB.trans_lt hB1))
    linarith only [hcircle, hexcess]

/-- MP.16 for the actual cap whenever its companion density is regular
on the displayed half-open arc. The whole family of interior angles is
retained in `sweptNiche`. -/
theorem IsDownwardCap.sweptNiche_le_circle_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ}
    {K α x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hA : 0 < companionInitialOffset U)
    (hAB : companionInitialOffset U ≤ x - horizontalLeft U)
    (hBα : x - horizontalLeft U < Real.sin α)
    (hsub : Ioc (Real.pi / 2)
      (Real.arcsin (x - horizontalLeft U) + Real.pi / 2) ⊆ S) :
    sweptNiche U α x ≤
      circleHeight (companionInitialOffset U) - circleHeight (x - horizontalLeft U) +
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
          (Real.arcsin (companionInitialOffset U)) := by
  have hbound (r : ℝ) (hr : r ∈ Icc 0 α) :=
    hU.max_secondWall_le_circle_of_density hρ hρ0 hρK heq
      hα0 hαL hA hAB hBα hsub hr
  apply sweptNiche_le_of_forall hα0
    ((le_max_right (secondWall U 0 x) 0).trans (hbound 0 ⟨le_rfl, hα0.le⟩))
  intro r hr
  exact ((min_le_right _ _).trans (le_max_left _ _)).trans
    (hbound r ⟨hr.1.le, hr.2.le⟩)

theorem IsDownwardCap.sweptNiche_le_circle_of_unit_prefix
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ}
    {K α x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hA : 0 < companionInitialOffset U)
    (hAB : companionInitialOffset U ≤ x - horizontalLeft U)
    (hBα : x - horizontalLeft U < Real.sin α)
    (hsub : Ioc (Real.pi / 2)
      (Real.arcsin (x - horizontalLeft U) + Real.pi / 2) ⊆ S)
    (hunit : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.arcsin (companionInitialOffset U))),
      ρ (t + Real.pi / 2) ≤ 1) :
    sweptNiche U α x ≤
      circleHeight (companionInitialOffset U) - circleHeight (x - horizontalLeft U) := by
  have h := hU.sweptNiche_le_circle_of_density hρ hρ0 hρK heq hα0 hαL hA hAB hBα hsub
  rwa [terminalWeightedExcess_eq_zero_of_unit_prefix (Real.arcsin_nonneg.mpr hA.le) hunit,
    add_zero] at h

end AmbidextrousSofa
