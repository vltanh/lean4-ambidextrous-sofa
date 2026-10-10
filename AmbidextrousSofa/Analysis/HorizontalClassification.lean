import AmbidextrousSofa.Analysis.CapNormalization
import AmbidextrousSofa.Analysis.HorizontalCalibration
import AmbidextrousSofa.Analysis.HorizontalWidthReduction

/-!
# Actual horizontal full-cap classification

The selected-source width theorem provides an orientation of the actual
maximum whose two genuine curvature densities are at most one. Its own
closed support pair therefore satisfies the exact geometric calibration.
Equality in the global comparison identifies the cap. Centering and the
orientation are then inverted at the level of literal sets.

The only geometric premises describe an actual height-one maximum with
a horizontal middle roof. No occupation, density, analytic comparison,
or equality conclusion is supplied as a hypothesis.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.horizontal_classification
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    capScore U (Real.pi / 2) = M / 2 ∧ capWidth U = 8 / 3 * Reference.A ∧
      ∃ b : ℝ, U = horizontalTranslate Reference.referenceCap b ∨
        horizontalMirror U = horizontalTranslate Reference.referenceCap b := by
  have hT := hU.centeredCap
  have hl : horizontalLeft (centeredCap U) = -2 * (capWidth U / 4) := by
    rw [horizontalLeft_centeredCap hU.isCap]
    ring
  have hr : horizontalRight (centeredCap U) = 2 * (capWidth U / 4) := by
    rw [horizontalRight_centeredCap hU.isCap]
    ring
  have hTheight : capHeight (centeredCap U) = 1 := by
    rw [capHeight_centeredCap hU.isCap, hheight]
  have hTmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft (centeredCap U))
      (horizontalRight (centeredCap U)), capRoof (centeredCap U) x = 1 :=
    hU.isCap.roof_eq_const_on_middle_horizontalTranslate hmiddle _
  obtain ⟨V, hVor, hV, _hlV, _hrV, hVheight, hVwidth, hVscore, hVmiddle,
      ρ, hρ, hρbound, heq⟩ :=
    hT.exists_horizontal_oriented_unit_density hl hr hTheight hTmiddle
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => (hρbound t).1
  have hρ1 : ∀ t, ρ t ≤ 1 := fun t => (hρbound t).2.1
  have hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1 :=
    Filter.Eventually.of_forall (fun t => ⟨hρ1 t, hρ1 (t + Real.pi / 2)⟩)
  have hscore := hV.capScore_eq_half_M_of_horizontal_unit_density
    hVheight hVmiddle hρ hρ0 hρ1 heq hunit
  obtain ⟨hwidth, b, hshape⟩ := hV.eq_reference_translate_of_horizontal_unit_density
    hVheight hVmiddle hρ hρ0 hρ1 heq hunit
  refine ⟨?_, ?_, ?_⟩
  · rw [hVscore, capScore_centeredCap hU.isCap] at hscore
    exact hscore
  · rw [hVwidth, capWidth_centeredCap hU.isCap] at hwidth
    exact hwidth
  · rcases hVor with hVor | hVor
    · rw [hVor] at hshape
      have h := eq_horizontalTranslate_of_horizontalTranslate_eq hshape
      exact ⟨_, Or.inl h⟩
    · rw [hVor, centeredCap, horizontalMirror_horizontalTranslate] at hshape
      have h := eq_horizontalTranslate_of_horizontalTranslate_eq hshape
      exact ⟨_, Or.inr h⟩

theorem IsFullCapMaximizer.capScore_eq_half_M_of_horizontal
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    capScore U (Real.pi / 2) = M / 2 := (hU.horizontal_classification hheight hmiddle).1

end AmbidextrousSofa
