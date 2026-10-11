module

public import AmbidextrousSofa.Analysis.HorizontalSupportArea
public import AmbidextrousSofa.Analysis.HorizontalSignedArea
public import AmbidextrousSofa.Analysis.AdaptiveGlobalComparison
public import AmbidextrousSofa.Geometry.UpwardSupport

@[expose] public section

/-!
# Calibration of the actual horizontal full maximum

The actual cap area and the actual signed niche area give the adaptive
functional of the cap's own closed support pair. The global analytic
comparison then bounds its literal spatial score. Equality identifies
both actual support functions, hence the actual cap, up to horizontal
translation. No analytic or geometric equality certificate is an input.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

namespace Analysis

theorem twice_adaptiveFunctional_eq_support_expression (u : QuarterPair) :
    2 * adaptiveFunctional u =
      (∫ t in (0 : ℝ)..(Real.pi / 2),
        (u.f t ^ 2 - u.fD t ^ 2) + (u.g t ^ 2 - u.gD t ^ 2)) +
      (∫ t in (0 : ℝ)..(Real.pi / 2), cornerDensity u.f u.g u.fD u.gD t) -
      (∫ t in (0 : ℝ)..(Real.pi / 2), min (supportP u.fD u.g t) 0 ^ 2) -
      ∫ t in (0 : ℝ)..(Real.pi / 2), max (supportQ u.gD u.f t) 0 ^ 2 := by
  have hi {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 (Real.pi / 2))) :=
    hF.intervalIntegrable_of_Icc (μ := volume) (by positivity)
  have hp : ContinuousOn (supportP u.fD u.g) (Icc 0 (Real.pi / 2)) :=
    (u.continuous_fD.fun_sub u.continuous_g).fun_add continuousOn_const
  have hq : ContinuousOn (supportQ u.gD u.f) (Icc 0 (Real.pi / 2)) :=
    (u.continuous_gD.fun_add u.continuous_f).fun_sub continuousOn_const
  have hE := hi (((u.continuous_f.fun_pow 2).fun_sub (u.continuous_fD.fun_pow 2)).fun_add
    ((u.continuous_g.fun_pow 2).fun_sub (u.continuous_gD.fun_pow 2)))
  have hC := hi (F := cornerDensity u.f u.g u.fD u.gD)
    (((u.continuous_f.fun_sub continuousOn_const).fun_mul hq).fun_sub
      ((u.continuous_g.fun_sub continuousOn_const).fun_mul hp))
  have hP := hi (F := fun t => min (supportP u.fD u.g t) 0 ^ 2)
    ((hp.inf continuousOn_const).fun_pow 2)
  have hQ := hi (F := fun t => max (supportQ u.gD u.f t) 0 ^ 2)
    ((hq.sup continuousOn_const).fun_pow 2)
  rw [← intervalIntegral.integral_add hE hC, ← intervalIntegral.integral_sub (hE.add hC) hP,
    ← intervalIntegral.integral_sub ((hE.add hC).sub hP) hQ, adaptiveFunctional,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [adaptiveDensity, QuarterPair.p, QuarterPair.q, cornerDensity, supportP, supportQ]
  ring

end Analysis

theorem IsFullCapMaximizer.capScore_eq_adaptive_of_horizontal_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) :
    let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
    capScore U (Real.pi / 2) = Analysis.adaptiveFunctional F - capWidth U / 2 := by
  have := Analysis.twice_adaptiveFunctional_eq_support_expression
    (horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq)
  have := hU.volumeReal_eq_horizontalSupportQuarterPair_energy hρ hρ0 hρK heq hheight hmiddle
  have := hU.twice_middle_niche_eq_signed_support hheight hmiddle hρ hρ0 hρK heq hunit
  have := hU.isCap.capScore_eq_volume_sub_middle_niche_of_horizontal hmiddle
  intro F
  linarith

theorem IsFullCapMaximizer.capScore_eq_half_M_of_horizontal_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) : capScore U (Real.pi / 2) = M / 2 := by
  obtain ⟨hf0, hg0, hfL, hgL, -⟩ :=
    hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle
  have hw : capWidth U = horizontalRight U - horizontalLeft U := rfl
  have hbound := Analysis.adaptiveFunctional_sub_halfWidth_le_half_M _ hfL hg0
    (by linarith [hU.two_lt_width])
  have hscore : capScore U (Real.pi / 2) = Analysis.adaptiveFunctional _ - capWidth U / 2 :=
    hU.capScore_eq_adaptive_of_horizontal_unit_density hheight hmiddle hρ hρ0 hρK heq hunit
  exact le_antisymm (by linarith) hU.reference_le

/-- Equality of the actual support functions identifies the downward
cap itself; all horizontal translation freedom is kept explicit. -/
theorem IsFullCapMaximizer.eq_reference_translate_of_horizontal_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) :
    capWidth U = 8 / 3 * Reference.A ∧
      ∃ b : ℝ, U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  obtain ⟨hf0, hg0, hfL, hgL, -⟩ :=
    hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle
  have hw : capWidth U = horizontalRight U - horizontalLeft U := rfl
  have hscore : capScore U (Real.pi / 2) = Analysis.adaptiveFunctional _ - capWidth U / 2 :=
    hU.capScore_eq_adaptive_of_horizontal_unit_density hheight hmiddle hρ hρ0 hρK heq hunit
  have hM :=
    hU.capScore_eq_half_M_of_horizontal_unit_density hheight hmiddle hρ hρ0 hρK heq hunit
  obtain ⟨hW, b, hf, hg⟩ := Analysis.eqOn_reference_translate_of_adaptiveFunctional_eq _ hfL hg0
    (by linarith [hU.two_lt_width]) (by linarith)
  have hRef := Reference.isDownwardCap_referenceCap
  refine ⟨by linarith, b, hU.isCap.eq_of_quarter_support_eq (hRef.horizontalTranslate b)
    (fun t ht => ?_) (fun t ht => ?_)⟩
  all_goals rw [AmbidextrousSofa.horizontalTranslate,
    support_translate hRef.isCompact hRef.nonempty]
  · rw [show support Reference.referenceCap (unitNormal t) = _
      from Reference.angleSupport_referenceCap_eq_f ht]
    exact (hf ht).trans (by simp [coordDot, unitNormal])
  · rw [companionNormal_eq_unitNormal, show
      support Reference.referenceCap (unitNormal (t + Real.pi / 2)) = _
      from Reference.angleSupport_referenceCap_eq_g ht]
    exact (hg ht).trans
      (by simp [coordDot, unitNormal, sub_eq_add_neg, Real.cos_add_pi_div_two])

end AmbidextrousSofa
