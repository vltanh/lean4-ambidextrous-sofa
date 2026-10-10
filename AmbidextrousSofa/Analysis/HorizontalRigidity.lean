module

public import AmbidextrousSofa.Analysis.HorizontalClassification
public import AmbidextrousSofa.Reference.HorizontalSymmetry

@[expose] public section

/-!
# Horizontal rigidity in the original orientation

The actual reference reflection identity removes the auxiliary orientation
chosen by the unit-curvature proof. Every actual horizontal full maximum
is a literal horizontal translate of the same displayed reference cap.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.eq_reference_translate_of_horizontal
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    ∃ b : ℝ, U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  obtain ⟨_hscore, _hwidth, b, h | h⟩ := hU.horizontal_classification hheight hmiddle
  · exact ⟨b, h⟩
  · exact ⟨_, Reference.eq_reference_translate_of_horizontalMirror_eq h⟩

end AmbidextrousSofa
