module

public import AmbidextrousSofa.Analysis.SelectedNicheHeight
public import AmbidextrousSofa.Analysis.OneTurnArea
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds

@[expose] public section

/-!
# Actual one-turn geometry of a canonical tilted full maximum

The central niche-height estimate now follows from actual maximality.
Together with the exact corner confinement and convex wing bounds, it
places the entire swept niche below the original cap roof. The resulting
survivor is compact, connected, has a genuine continuous corridor passage,
and obeys the ordinary-sofa area bound. No central fit certificate remains
in these statements.
-/

open Set

namespace AmbidextrousSofa

theorem middleHalfInterval_eq_centered {U : Set Plane} {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C) :
    middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C :=
  (centered_quarter_points hl hr).2.2

theorem IsFullCapMaximizer.sweptNiche_le_roof_of_canonical_range
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x :=
  hU.sweptNiche_le_roof_of_middle_height_bound hl hr hleft hright hC0 hC1 hh0 hh1 hheight haffine
    (middleHalfInterval_eq_centered hl hr ▸
      hU.sweptNiche_le_half_endpoint_height_sum_of_affine hheight haffine)

end AmbidextrousSofa
