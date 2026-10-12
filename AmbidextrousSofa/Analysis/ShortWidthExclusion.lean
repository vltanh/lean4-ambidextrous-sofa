module

public import AmbidextrousSofa.Analysis.ThreeAngleShortWidth

@[expose] public section

/-!
# Actual short-width cap exclusion

Every barrier whose visited range reaches the nearby complementary corner
lies above the three-angle barrier, so the three-angle short-width
exclusion bounds the actual cap score. All support and area inequalities
are derived from the cap itself. No calibrated-profile or
scalar-comparison hypothesis is supplied by the caller.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- Every actual cap in this centered, height-one canonical form and
short-width range has score strictly below the reference comparison
level. The conclusion applies to full and sufficiently long proper turns. -/
theorem IsDownwardCap.capScore_lt_half_M_of_short_width
    {U : Set Plane} (hU : IsDownwardCap U) {a h α : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 ≤ h)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hαnear : Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) ≤ α)
    (hαL : α ≤ Real.pi / 2) : capScore U α < M / 2 :=
  ((hU.capScore_le_threeAngleScore hαnear hαL).trans_lt
    (hU.threeAngleScore_lt_of_short_width ha ha1 hh hl hr hleft hright haffine)).trans
      referenceHalfAreaLower_lt_half_M

end AmbidextrousSofa
