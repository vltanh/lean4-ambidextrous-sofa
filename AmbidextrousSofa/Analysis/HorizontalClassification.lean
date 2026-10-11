module

public import AmbidextrousSofa.Analysis.CapNormalization
public import AmbidextrousSofa.Analysis.HorizontalCalibration
public import AmbidextrousSofa.Analysis.HorizontalWidthReduction

@[expose] public section

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
      ∃ b : ℝ, U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b ∨
        AmbidextrousSofa.horizontalMirror U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  have hl : horizontalLeft (AmbidextrousSofa.centeredCap U) = -2 * (capWidth U / 4) := by
    rw [horizontalLeft_centeredCap hU.isCap]; ring
  have hr : horizontalRight (AmbidextrousSofa.centeredCap U) = 2 * (capWidth U / 4) := by
    rw [horizontalRight_centeredCap hU.isCap]; ring
  have hh : capHeight (AmbidextrousSofa.centeredCap U) = 1 := by
    rw [capHeight_centeredCap hU.isCap, hheight]
  have hm := hU.isCap.roof_eq_const_on_middle_horizontalTranslate hmiddle
    (-(horizontalLeft U + horizontalRight U) / 2)
  obtain ⟨V, hVor, hV, -, -, hVheight, hVwidth, hVscore, hVmiddle, ρ, hρ, hρbound, heq⟩ :=
    hU.centeredCap.exists_horizontal_oriented_unit_density_of_width_le hl hr
      (div_nonneg hU.isCap.capWidth_nonneg (by norm_num))
      (hU.centeredCap.horizontal_quarter_width_le hl hr hh hm) hh hm
  have hρ0 (t : ℝ) := (hρbound t).1
  have hρ1 (t : ℝ) := (hρbound t).2.1
  have hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1 := .of_forall fun t => ⟨hρ1 t, hρ1 _⟩
  obtain ⟨hM, hwidth, b, hshape⟩ := hV.eq_reference_translate_of_horizontal_unit_density
    hVheight hVmiddle hρ hρ0 hρ1 heq hunit
  refine ⟨by rw [← capScore_centeredCap hU.isCap, ← hVscore, hM],
    by rwa [hVwidth, capWidth_centeredCap hU.isCap] at hwidth, ?_⟩
  rcases hVor with rfl | rfl
  · exact ⟨_, .inl (eq_horizontalTranslate_of_horizontalTranslate_eq hshape)⟩
  · rw [AmbidextrousSofa.centeredCap, horizontalMirror_horizontalTranslate] at hshape
    exact ⟨_, .inr (eq_horizontalTranslate_of_horizontalTranslate_eq hshape)⟩

end AmbidextrousSofa
