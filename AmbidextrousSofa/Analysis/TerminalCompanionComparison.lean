module

public import AmbidextrousSofa.Analysis.TerminalCompanionCurvature
public import AmbidextrousSofa.Analysis.TerminalCircleMargin

@[expose] public section

/-!
# The actual companion-wall circle comparison

The literal curvature measure determines both companion-coordinate
moments. The actual supporting point at a localized positive wall
maximum then supplies the horizontal moment and the wall height. This
proves the weighted circle estimate for the whole visited niche, for a cap
whose curvature has a bounded density on the companion arc.
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
  have hB1 : x - horizontalLeft U < 1 := hBα.trans_le (Real.sin_le_one α)
  by_cases hpositive : ∃ t ∈ Icc 0 α, 0 < secondWall U t x
  · obtain ⟨t, ht, htB, hmax, hX, hY⟩ :=
      hU.exists_positive_localized_secondWall_max hα0 hαL (hA.le.trans hAB) hBα le_rfl hpositive
    -- The moments run from the left endpoint of the top face, at the cap height.
    obtain ⟨h1, h2⟩ := hU.shiftedCompanion_sub_eq_integral_of_density hρ hρ0 hρK heq ht.1.le
      (by simpa only [zero_add] using (Ioc_subset_Ioc le_rfl (add_le_add_left htB _)).trans hsub)
    simp only [shiftedCompanionX, shiftedCompanionY, zero_add, Real.sin_zero, Real.cos_zero,
      add_zero, top_vplus_snd_eq_capHeight] at h1 h2
    exact (max_le_max (hmax hr) le_rfl).trans (terminal_weighted_companion_height_bound hA hAB hB1
      ht.1.le htB (intervalIntegrable_bounded_real_density (hρ.comp (measurable_id.add_const _))
        (fun _ => hρ0 _) (fun _ => hρK _) _ _) (ae_of_all _ fun _ => hρ0 _)
      (by unfold companionInitialOffset; linarith) hU.companionInitialDeficit_nonneg
      (by unfold companionInitialDeficit; linarith))
  · rw [max_eq_right (le_of_not_gt fun h => hpositive ⟨r, hr, h⟩)]
    linarith [circleHeight_antitoneOn ⟨hA, hAB.trans_lt hB1⟩ ⟨hA.trans_le hAB, hB1⟩ hAB,
      terminalWeightedExcess_nonneg (v := fun t => ρ (t + Real.pi / 2))
        (Real.arcsin_nonneg.mpr hA.le) (Real.arcsin_lt_pi_div_two.mpr (hAB.trans_lt hB1))]

end AmbidextrousSofa
