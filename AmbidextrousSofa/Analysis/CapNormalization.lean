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
  ext p
  rw [mem_horizontalTranslate_iff]
  simp

theorem horizontalTranslate_add (U : Set Plane) (a b : ℝ) :
    horizontalTranslate (horizontalTranslate U a) b = horizontalTranslate U (a + b) := by
  ext p
  simp only [mem_horizontalTranslate_iff]
  change (p.1 - b - a, p.2) ∈ U ↔ (p.1 - (a + b), p.2) ∈ U
  rw [show p.1 - b - a = p.1 - (a + b) by ring]

theorem eq_horizontalTranslate_of_horizontalTranslate_eq
    {U V : Set Plane} {a b : ℝ}
    (h : horizontalTranslate U a = horizontalTranslate V b) :
    U = horizontalTranslate V (b - a) := by
  have hinv := congrArg (fun S : Set Plane => horizontalTranslate S (-a)) h
  simpa only [horizontalTranslate_add, add_neg_cancel, horizontalTranslate_zero,
    sub_eq_add_neg] using hinv

theorem horizontalMirror_horizontalTranslate (U : Set Plane) (a : ℝ) :
    horizontalMirror (horizontalTranslate U a) = horizontalTranslate (horizontalMirror U) (-a) := by
  ext p
  simp only [mem_horizontalMirror_iff, mem_horizontalTranslate_iff]
  change (-p.1 - a, p.2) ∈ U ↔ (-(p.1 - -a), p.2) ∈ U
  rw [show -p.1 - a = -(p.1 - -a) by ring]

theorem capHeight_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (a : ℝ) :
    capHeight (horizontalTranslate U a) = capHeight U := by
  unfold capHeight horizontalTranslate
  rw [support_translate hU.isCompact hU.nonempty]
  simp [coordDot]

theorem capHeight_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    capHeight (centeredCap U) = capHeight U := capHeight_horizontalTranslate hU _

theorem capWidth_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    capWidth (centeredCap U) = capWidth U := capWidth_horizontalTranslate hU _

theorem IsDownwardCap.roof_eq_const_on_middle_horizontalTranslate
    {U : Set Plane} (hU : IsDownwardCap U) {H : ℝ}
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = H)
    (a : ℝ) :
    ∀ x ∈ middleHalfInterval (horizontalLeft (AmbidextrousSofa.horizontalTranslate U a))
      (horizontalRight (AmbidextrousSofa.horizontalTranslate U a)), capRoof (AmbidextrousSofa.horizontalTranslate U a) x = H := by
  intro x hx
  rw [horizontalLeft_horizontalTranslate hU, horizontalRight_horizontalTranslate hU,
    middleHalfInterval_add] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [capRoof_horizontalTranslate, add_sub_cancel_right]
  exact hmiddle y hy

theorem IsFullCapMaximizer.horizontalTranslate {U : Set Plane}
    (hU : IsFullCapMaximizer U) (a : ℝ) : IsFullCapMaximizer (AmbidextrousSofa.horizontalTranslate U a) :=
  hU.of_score_le (hU.isCap.horizontalTranslate a) (capScore_horizontalTranslate hU.isCap a _).ge

theorem IsFullCapMaximizer.centeredCap {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsFullCapMaximizer (AmbidextrousSofa.centeredCap U) := hU.horizontalTranslate _

end AmbidextrousSofa
