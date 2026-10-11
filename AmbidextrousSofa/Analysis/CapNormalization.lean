module

public import AmbidextrousSofa.Analysis.CapReflection

@[expose] public section

/-!
# Reversible horizontal normalization of actual caps

Horizontal translations preserve height, the literal middle roof, and
global maximality. Their inverse and reflection identities let a
classification proved in centered coordinates recover the original set.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

@[simp] theorem horizontalTranslate_zero (U : Set Plane) : horizontalTranslate U 0 = U := by
  simp [horizontalTranslate, Prod.mk_zero_zero]

theorem horizontalTranslate_add (U : Set Plane) (a b : ℝ) :
    horizontalTranslate (horizontalTranslate U a) b = horizontalTranslate U (a + b) := by
  simp [horizontalTranslate, image_image, add_assoc, -image_add_right]

theorem eq_horizontalTranslate_of_horizontalTranslate_eq {U V : Set Plane} {a b : ℝ}
    (h : horizontalTranslate U a = horizontalTranslate V b) :
    U = horizontalTranslate V (b - a) := by
  simpa only [horizontalTranslate_add, add_neg_cancel, horizontalTranslate_zero,
    sub_eq_add_neg] using congrArg (horizontalTranslate · (-a)) h

theorem horizontalMirror_horizontalTranslate (U : Set Plane) (a : ℝ) :
    horizontalMirror (horizontalTranslate U a) = horizontalTranslate (horizontalMirror U) (-a) := by
  ext p
  simp [mem_horizontalMirror_iff, mem_horizontalTranslate_iff, horizontalReflection,
    sub_eq_add_neg, add_comm]

theorem capHeight_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    capHeight (centeredCap U) = capHeight U := by
  simp [capHeight, centeredCap, horizontalTranslate, support_translate hU.isCompact hU.nonempty,
    coordDot, -image_add_right]

theorem capWidth_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    capWidth (centeredCap U) = capWidth U := capWidth_horizontalTranslate hU _

theorem IsDownwardCap.roof_eq_const_on_middle_horizontalTranslate
    {U : Set Plane} (hU : IsDownwardCap U) {H : ℝ}
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = H)
    (a : ℝ) :
    ∀ x ∈ middleHalfInterval (horizontalLeft (AmbidextrousSofa.horizontalTranslate U a))
      (horizontalRight (AmbidextrousSofa.horizontalTranslate U a)),
        capRoof (AmbidextrousSofa.horizontalTranslate U a) x = H := by
  rw [horizontalLeft_horizontalTranslate hU, horizontalRight_horizontalTranslate hU,
    middleHalfInterval_add, forall_mem_image]
  simpa [capRoof_horizontalTranslate] using hmiddle

theorem IsFullCapMaximizer.horizontalTranslate {U : Set Plane}
    (hU : IsFullCapMaximizer U) (a : ℝ) :
    IsFullCapMaximizer (AmbidextrousSofa.horizontalTranslate U a) :=
  hU.of_score_le (hU.isCap.horizontalTranslate a) (capScore_horizontalTranslate hU.isCap a _).ge

theorem IsFullCapMaximizer.centeredCap {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsFullCapMaximizer (AmbidextrousSofa.centeredCap U) := hU.horizontalTranslate _

end AmbidextrousSofa
