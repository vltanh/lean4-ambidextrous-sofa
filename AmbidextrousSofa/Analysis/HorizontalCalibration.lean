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
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hp : ContinuousOn (supportP u.fD u.g) (Icc 0 (Real.pi / 2)) :=
    (u.continuous_fD.sub u.continuous_g).add continuousOn_const
  have hq : ContinuousOn (supportQ u.gD u.f) (Icc 0 (Real.pi / 2)) :=
    (u.continuous_gD.add u.continuous_f).sub continuousOn_const
  have hE : ContinuousOn (fun t =>
      (u.f t ^ 2 - u.fD t ^ 2) + (u.g t ^ 2 - u.gD t ^ 2)) (Icc 0 (Real.pi / 2)) :=
    ((u.continuous_f.pow 2).sub (u.continuous_fD.pow 2)).add
      ((u.continuous_g.pow 2).sub (u.continuous_gD.pow 2))
  have hC : ContinuousOn (cornerDensity u.f u.g u.fD u.gD) (Icc 0 (Real.pi / 2)) :=
    ((u.continuous_f.sub continuousOn_const).mul hq).sub
      ((u.continuous_g.sub continuousOn_const).mul hp)
  have hEi := ContinuousOn.intervalIntegrable_of_Icc hL hE
  have hCi := ContinuousOn.intervalIntegrable_of_Icc hL hC
  have hPi : IntervalIntegrable
      (fun t => min (supportP u.fD u.g t) 0 ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL ((hp.min continuousOn_const).pow 2)
  have hQi : IntervalIntegrable
      (fun t => max (supportQ u.gD u.f t) 0 ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL ((hq.max continuousOn_const).pow 2)
  calc
    _ = ∫ t in (0 : ℝ)..(Real.pi / 2), 2 * adaptiveDensity u t := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = ∫ t in (0 : ℝ)..(Real.pi / 2),
        ((u.f t ^ 2 - u.fD t ^ 2) + (u.g t ^ 2 - u.gD t ^ 2)) +
        cornerDensity u.f u.g u.fD u.gD t -
        min (supportP u.fD u.g t) 0 ^ 2 - max (supportQ u.gD u.f t) 0 ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      unfold adaptiveDensity QuarterPair.p QuarterPair.q cornerDensity supportP supportQ
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hEi.add hCi).sub hPi) hQi,
        intervalIntegral.integral_sub (hEi.add hCi) hPi,
        intervalIntegral.integral_add hEi hCi]

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
  let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
  have hsplit := Analysis.twice_adaptiveFunctional_eq_support_expression F
  have harea := hU.volumeReal_eq_horizontalSupportQuarterPair_energy
    hρ hρ0 hρK heq hheight hmiddle
  have hniche := hU.twice_middle_niche_eq_signed_support hheight hmiddle hρ hρ0 hρK heq hunit
  have hscore := hU.isCap.capScore_eq_volume_sub_middle_niche_of_horizontal hmiddle
  nlinarith

theorem IsFullCapMaximizer.capScore_eq_half_M_of_horizontal_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) : capScore U (Real.pi / 2) = M / 2 := by
  let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
  rcases hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle with
    ⟨hf0, hg0, hfL, hgL, _⟩
  have hspan : F.f 0 + F.g (Real.pi / 2) = capWidth U := by
    rw [hf0, hgL]
    dsimp only [capWidth]
    ring
  have hwidth : 8 / 5 ≤ F.f 0 + F.g (Real.pi / 2) := by
    rw [hspan]
    linarith only [hU.two_lt_width]
  have hbound := Analysis.adaptiveFunctional_sub_halfWidth_le_half_M F hfL hg0 hwidth
  rw [hspan] at hbound
  have hscore := hU.capScore_eq_adaptive_of_horizontal_unit_density
    hheight hmiddle hρ hρ0 hρK heq hunit
  exact le_antisymm (by linarith only [hbound, hscore]) hU.reference_le

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
  let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
  rcases hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle with
    ⟨hf0, hg0, hfL, hgL, _⟩
  have hspan : F.f 0 + F.g (Real.pi / 2) = capWidth U := by
    rw [hf0, hgL]
    dsimp only [capWidth]
    ring
  have hwidth : 8 / 5 ≤ F.f 0 + F.g (Real.pi / 2) := by
    rw [hspan]
    linarith only [hU.two_lt_width]
  have hscore := hU.capScore_eq_half_M_of_horizontal_unit_density
    hheight hmiddle hρ hρ0 hρK heq hunit
  have hcal := hU.capScore_eq_adaptive_of_horizontal_unit_density
    hheight hmiddle hρ hρ0 hρK heq hunit
  have hadaptive : Analysis.adaptiveFunctional F - (F.f 0 + F.g (Real.pi / 2)) / 2 = M / 2 := by
    rw [hspan]
    linarith only [hcal, hscore]
  obtain ⟨hW, b, hf, hg⟩ :=
    Analysis.eqOn_reference_translate_of_adaptiveFunctional_eq F hfL hg0 hwidth hadaptive
  refine ⟨by rwa [hspan] at hW, b, ?_⟩
  have hRef := Reference.isDownwardCap_referenceCap
  apply hU.isCap.eq_of_quarter_support_eq (hRef.horizontalTranslate b)
  · intro t ht
    calc
      support U (unitNormal t) = Reference.referenceF t + b * Real.cos t := hf ht
      _ = support (AmbidextrousSofa.horizontalTranslate Reference.referenceCap b) (unitNormal t) := by
        rw [AmbidextrousSofa.horizontalTranslate, support_translate hRef.isCompact hRef.nonempty]
        change Reference.referenceF t + b * Real.cos t =
          angleSupport Reference.referenceCap t + coordDot (b, 0) (unitNormal t)
        rw [Reference.angleSupport_referenceCap_eq_f ht]
        simp only [coordDot, unitNormal, zero_mul, add_zero]
  · intro t ht
    calc
      support U (companionNormal t) = Reference.referenceG t - b * Real.sin t := by
        rw [companionNormal_eq_unitNormal]
        exact hg ht
      _ = support (AmbidextrousSofa.horizontalTranslate Reference.referenceCap b) (companionNormal t) := by
        rw [AmbidextrousSofa.horizontalTranslate, support_translate hRef.isCompact hRef.nonempty]
        have href : support Reference.referenceCap (companionNormal t) = Reference.referenceG t := by
          rw [companionNormal_eq_unitNormal]
          exact Reference.angleSupport_referenceCap_eq_g ht
        rw [href]
        simp only [coordDot, companionNormal, zero_mul, add_zero, mul_neg]
        ring

end AmbidextrousSofa
