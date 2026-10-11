module

public import AmbidextrousSofa.Analysis.ThreeAngleComparison
public import AmbidextrousSofa.Analysis.ThreeAngleShortWidth
public import AmbidextrousSofa.Analysis.ThreeAngleWideWidth
public import AmbidextrousSofa.Analysis.ThreeAngleTriangleWidth

@[expose] public section

/-!
# Width and tilt from the actual finite comparison

This assembly receives literal endpoint heights and the two nonnegative
values occurring in their pressure identities. It makes no assertion
that these values come from the outgoing barrier of a reflected cap.
The three-angle objective itself is reflection invariant.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.threeAngle_width_bounds_of_endpoint_laws {U : Set Plane}
    (hU : IsDownwardCap U) {a h qR qL : ℝ}
    (ha0 : 0 < a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hqR : 0 ≤ qR) (hqL : 0 ≤ qL)
    (hEPR : capRoof U a = 1 / 2 + h / 4 + (3 * qR - qL) / 4)
    (hEPL : capRoof U (-a) = 1 / 2 - 3 * h / 4 + (3 * qL - qR) / 4)
    (hscore : 41 / 50 ≤ threeAngleComparisonScore U) :
    1001 / 1000 < a ∧ a < 37 / 25 ∧ h < 17 / 50 := by
  -- The endpoint laws give lower bounds on the two endpoint heights.
  have hceiling := hU.capRoof_le_tiltedAffineCeiling ha0 hl hr hleft hright haffine (-a)
    ((hl ▸ hr ▸ hU.horizontalProjection_eq_Icc) ▸ ⟨le_rfl, by linarith only [ha0]⟩)
  rw [tiltedAffineCeiling, mul_neg, div_mul_cancel₀ h ha0.ne'] at hceiling
  obtain ⟨hER, hEL, hEP⟩ := partialTriangle_endpoint_lower_bounds hqR hqL hEPR hEPL
    (capRoof_le_one hU.isCompact hU.inStrip a) (by linarith only [hceiling])
  -- Each width range below excludes the score `41 / 50`.
  have haShort : 1001 / 1000 < a := lt_of_not_ge fun h' => not_lt_of_ge hscore
    (hU.threeAngleScore_lt_of_short_width ha0 h' hh0 hl hr hleft hright haffine)
  have haWide : a < 8 / 5 := lt_of_not_ge fun h' => not_lt_of_ge hscore
    (hU.threeAngleScore_lt_of_wide_width_and_endpoint_bounds h' ha1 hh0 hh1 hl hr hleft hright
      haffine hEP (by linarith only [hER, hh0]) (by linarith only [hEL, hh0]))
  have hhTilt := (hU.threeAngle_intermediate_width_tilt_bound (by linarith only [haShort])
    haWide.le hh0 hh1 hl hr hleft hright haffine hscore).1
  exact ⟨haShort, lt_of_not_ge fun h' => not_lt_of_ge hscore
    (hU.threeAngleScore_lt_of_full_triangles_and_endpoint_bounds h' haWide.le hh0 hhTilt.le
      hl hr hleft hright haffine hEP hER hEL), hhTilt⟩

end AmbidextrousSofa
