module

public import AmbidextrousSofa.Analysis.WideGainScalar

@[expose] public section

/-!
# Fitting the actual two wide niche pieces

The middle endpoint support points place both two-wall peaks inside the
middle window. Nonnegative actual support deficits place their crossovers
on opposite sides of the diagonal apex. The endpoint pressure identities
pay for both baseline truncation losses.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem wideNearRightIntercept_eq {U : Set Plane} {a h : ℝ}
    (ha : 0 < a) (hha : h < a) (k v : ℝ) :
    wideNearRightIntercept U k = 1 - nearDiagonalNorm k + k * v -
      wideLeftSupportDeficit U a h k v - wideLeftTiltPenalty a h k v := by
  rw [wideNearRightIntercept, wideLeftSupportDeficit, ← wideLeftTiltPenalty_identity ha hha k v]
  ring

theorem wideNearLeftIntercept_eq (U : Set Plane) (k u : ℝ) :
    wideNearLeftIntercept U k = 1 - nearDiagonalNorm k + k * u - nearDiagonalRightDeficit U k u := by
  rw [wideNearLeftIntercept, nearDiagonalRightDeficit]
  ring

theorem IsDownwardCap.wide_near_intercepts_lower {U : Set Plane}
    (hU : IsDownwardCap U) {a h k : ℝ} (ha : 0 < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    1 - h - nearDiagonalNorm k + k * a / 2 ≤ wideNearRightIntercept U k ∧
      1 - nearDiagonalNorm k + k * a / 2 ≤ wideNearLeftIntercept U k := by
  have hproj := (hl ▸ hr ▸ hU.horizontalProjection_eq_Icc).superset
  have hL := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact (x := -a / 2)
    (hproj ⟨by linarith only [ha], by linarith only [ha]⟩)) (-k, 1)
  have hR := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact (x := a / 2)
    (hproj ⟨by linarith only [ha], by linarith only [ha]⟩)) (k, 1)
  simp only [coordDot] at hL hR
  rw [wideNearRightIntercept, wideNearLeftIntercept]
  constructor <;> linarith only [hL, hR, hleft, hright]

/-- Both peak and crossover conditions for the literal support walls.
The weighted peak span comes from the diagonal endpoint budget. -/
theorem IsDownwardCap.wide_piece_fitting {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hspan : (1 - k / 2) * a + h < (1 + k) * nearDiagonalNorm k)
    (hk0 : diagonalOffsetLower < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 + v)
    (hvv : v ∈ Icc (a / 2 - h) (a - 3 * h / 2))
    (hm : a - 1 / 2 - h / 4 ≤ (u + v) / 2) :
    (u - v) / 2 ≤ wideCrossing k u (wideNearRightIntercept U k) ∧
      -(u - v) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k) ∧
      widePeak k (wideNearRightIntercept U k) (wideEndpointIntercept a (capRoof U a) k) ≤ a / 2 ∧
      widePeak k (wideNearLeftIntercept U k) (wideEndpointIntercept a (capRoof U (-a)) k) ≤ a / 2 := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have ha0 : 0 < a := by linarith only [ha]
  have hk : 0 < k := by linarith only [hk0]
  have hha : h < a := by linarith only [ha, hh1]
  have hNorm := wide_norm_rational_bounds hk0 hk1
  have hδR := hU.nearDiagonalRightDeficit_mem ha0 hk.le (by linarith only [hk1]) hl hr hright hu
  have hδL := hU.wideLeftSupportDeficit_mem ha0 hha (by linarith only [hk1])
    ((div_le_iff₀ ha0).mpr (by linarith only [mul_nonneg (sub_nonneg.2 ha) hk.le, hk0, hh1]))
    hl hr hleft hright haffine hv
  have hτ := wideLeftTiltPenalty_bounds ha0 hh (by linarith only [hk1])
    (wideLeftIntersection_mem ha0 hha hvv.1 hvv.2)
  have hmid : 3 / 4 ≤ (u + v) / 2 := by linarith only [hm, ha, hh1]
  have hcrossR := wide_crossing_after_apex (u := u) (w := v) (h := 0)
    (b := wideNearRightIntercept U k) hk hk1 hNorm.1 le_rfl (by linarith only [hmid])
    (by linarith only [wideNearRightIntercept_eq (U := U) ha0 hha k v, hδL.1, hτ.1])
  have hcrossL := wide_crossing_after_apex (u := v) (w := u) (h := 0)
    (b := wideNearLeftIntercept U k) hk hk1 hNorm.1 le_rfl (by linarith only [hmid])
    (by linarith only [wideNearLeftIntercept_eq U k u, hδR.1])
  have hpoints := hU.wide_near_intercepts_lower ha0 hl hr hleft hright (k := k)
  exact ⟨hcrossR.le, by linarith only [hcrossL],
    wide_peak_fits hk hksq hspan.le
      (capRoof_le_one hU.isCompact hU.inStrip a) hpoints.1,
    wide_peak_fits hk hksq hspan.le
      (capRoof_le_one hU.isCompact hU.inStrip (-a)) (by linarith only [hpoints.2, hh])⟩

end AmbidextrousSofa
