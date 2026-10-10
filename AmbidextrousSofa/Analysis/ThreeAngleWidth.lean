import AmbidextrousSofa.Analysis.ThreeAngleShortWidth
import AmbidextrousSofa.Analysis.ThreeAngleWideWidth
import AmbidextrousSofa.Analysis.ThreeAngleTriangleWidth

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

theorem IsDownwardCap.threeAngle_endpoint_bounds_of_laws {U : Set Plane}
    (hU : IsDownwardCap U) {a h qR qL : ℝ} (ha : 0 < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hqR : 0 ≤ qR) (hqL : 0 ≤ qL)
    (hEPR : capRoof U a = 1 / 2 + h / 4 + (3 * qR - qL) / 4)
    (hEPL : capRoof U (-a) = 1 / 2 - 3 * h / 4 + (3 * qL - qR) / 4) :
    1 / 3 + h / 2 ≤ capRoof U a ∧
      1 / 3 - 2 * h / 3 ≤ capRoof U (-a) ∧
      1 - h / 2 ≤ capRoof U a + capRoof U (-a) := by
  have hx : -a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    exact ⟨le_rfl, by linarith only [ha]⟩
  have hceiling := hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine (-a) hx
  have hza : (h / a) * a = h := div_mul_cancel₀ h ha.ne'
  have heL : capRoof U (-a) ≤ 1 - 3 * h / 2 := by
    unfold tiltedAffineCeiling at hceiling
    nlinarith only [hceiling, hza]
  exact partialTriangle_endpoint_lower_bounds hqR hqL hEPR hEPL
    (capRoof_le_one hU.isCompact hU.inStrip a) heL

theorem IsDownwardCap.threeAngle_width_bounds_of_endpoint_bounds {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 0 < a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hER : 1 / 3 + h / 2 ≤ capRoof U a)
    (hEL : 1 / 3 - 2 * h / 3 ≤ capRoof U (-a))
    (hscore : 41 / 50 ≤ threeAngleComparisonScore U) :
    1001 / 1000 < a ∧ a < 37 / 25 ∧ h < 17 / 50 := by
  have haShort : 1001 / 1000 < a := by
    by_contra hbad
    exact (not_lt_of_ge hscore)
      (hU.threeAngleScore_lt_of_short_width ha0 (le_of_not_gt hbad) hh0
        hl hr hleft hright haffine)
  have haWide : a < 8 / 5 := by
    by_contra hbad
    exact (not_lt_of_ge hscore)
      (hU.threeAngleScore_lt_of_wide_width_and_endpoint_bounds (le_of_not_gt hbad) ha1 hh0 hh1
        hl hr hleft hright haffine hEP
        (by linarith only [hER, hh0]) (by linarith only [hEL, hh0]))
  have hhTilt := (hU.threeAngle_intermediate_width_tilt_bound
    (by linarith only [haShort]) haWide.le hh0 hh1 hl hr hleft hright haffine hscore).1
  refine ⟨haShort, ?_, hhTilt⟩
  by_contra hbad
  exact (not_lt_of_ge hscore)
    (hU.threeAngleScore_lt_of_full_triangles_and_endpoint_bounds (le_of_not_gt hbad)
      haWide.le hh0 hhTilt.le hl hr hleft hright haffine hEP hER hEL)

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
  obtain ⟨hER, hEL, hEP⟩ := hU.threeAngle_endpoint_bounds_of_laws ha0 hl hr hleft hright
    haffine hqR hqL hEPR hEPL
  exact hU.threeAngle_width_bounds_of_endpoint_bounds ha0 ha1 hh0 hh1
    hl hr hleft hright haffine hEP hER hEL hscore

end AmbidextrousSofa
