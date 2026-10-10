import AmbidextrousSofa.Analysis.WideGainScalar
import AmbidextrousSofa.Analysis.NicheBoxBounds

/-!
# Fitting the actual two wide niche pieces

The middle endpoint support points place both two-wall peaks inside the
middle window. Nonnegative actual support deficits place their crossovers
on opposite sides of the diagonal apex. The endpoint pressure identities
and a unit-box bound pay for both baseline truncation losses.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem nine_tenths_one_third_circle {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcircle : c ^ 2 + s ^ 2 = 1) : (9 / 10) * c + s / 3 ≤ 1 := by
  have hsq : ((9 / 10) * c + s / 3) ^ 2 ≤ 829 / 900 := by
    nlinarith only [hcircle, sq_nonneg (c / 3 - (9 / 10) * s)]
  by_contra h
  have hgt : 1 < (9 / 10) * c + s / 3 := lt_of_not_ge h
  have hp := mul_pos (sub_pos.mpr hgt)
    (show 0 < (9 / 10) * c + s / 3 + 1 by linarith only [hgt])
  nlinarith only [hsq, hp]

theorem IsDownwardCap.middle_niche_le_two_thirds_of_box
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1) (hC : C ≤ 9 / 10) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 2 / 3 ∧
      sweptNiche U (Real.pi / 2) C ≤ 2 / 3 := by
  constructor
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (by norm_num)
    intro t ht
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    have hsupport := hU.support_companionNormal_le_centeredBox hbox hs.le hc.le
    have hcmul := mul_le_mul_of_nonneg_right hC hs.le
    have hcircle := nine_tenths_one_third_circle hc.le hs.le
      (by linarith only [Real.cos_sq_add_sin_sq t])
    apply (min_le_right (firstWall U t (-C)) (secondWall U t (-C))).trans
    rw [secondWall, div_le_iff₀ hc]
    nlinarith only [hsupport, hcmul, hcircle]
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (by norm_num)
    intro t ht
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    have hsupport := hU.support_unitNormal_le_centeredBox hbox hs.le hc.le
    have hcmul := mul_le_mul_of_nonneg_right hC hc.le
    have hcircle := nine_tenths_one_third_circle hs.le hc.le (Real.cos_sq_add_sin_sq t)
    apply (min_le_left (firstWall U t C) (secondWall U t C)).trans
    rw [firstWall, div_le_iff₀ hs]
    nlinarith only [hsupport, hcmul, hcircle]

theorem wideNearRightIntercept_eq {U : Set Plane} {a h : ℝ}
    (ha : 0 < a) (hha : h < a) (k v : ℝ) :
    wideNearRightIntercept U k = 1 - nearDiagonalNorm k + k * v -
      wideLeftSupportDeficit U a h k v - wideLeftTiltPenalty a h k v := by
  have h := wideLeftTiltPenalty_identity ha hha k v
  unfold wideNearRightIntercept wideLeftSupportDeficit
  linarith only [h]

theorem wideNearLeftIntercept_eq (U : Set Plane) (k u : ℝ) :
    wideNearLeftIntercept U k = 1 - nearDiagonalNorm k + k * u - nearDiagonalRightDeficit U k u := by
  unfold wideNearLeftIntercept nearDiagonalRightDeficit
  ring

theorem IsDownwardCap.wide_near_intercepts_lower {U : Set Plane}
    (hU : IsDownwardCap U) {a h k : ℝ} (ha : 0 < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    1 - h - nearDiagonalNorm k + k * a / 2 ≤ wideNearRightIntercept U k ∧
      1 - nearDiagonalNorm k + k * a / 2 ≤ wideNearLeftIntercept U k := by
  have hxL : -a / 2 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith only [ha]
  have hxR : a / 2 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith only [ha]
  have hL := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hxL) (-k, 1)
  have hR := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hxR) (k, 1)
  rw [hleft] at hL
  rw [hright] at hR
  simp only [coordDot, mul_neg, mul_one] at hL hR
  unfold wideNearRightIntercept wideNearLeftIntercept
  constructor <;> nlinarith only [hL, hR]

/-- Both peak and crossover conditions for the literal support walls.
The compact box comes from the earlier actual wide-score estimate. -/
theorem IsDownwardCap.wide_piece_fitting {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h) (hh1 : h < 1 / 4) (hah : a + h < 37 / 20)
    (hk0 : 41 / 100 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
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
  have ha0 : 0 < a := by linarith only [ha]
  have hk : 0 < k := by linarith only [hk0]
  have hha : h < a := by linarith only [ha, hh1]
  have hzk : h / a ≤ k := by
    apply (div_le_iff₀ ha0).mpr
    have hp := mul_nonneg (show 0 ≤ a - 8 / 5 by linarith only [ha]) hk.le
    nlinarith only [hp, hk0, hh1]
  have hNorm := wide_norm_rational_bounds hk0 hk1
  have hδR := hU.nearDiagonalRightDeficit_mem ha0 hk.le (by linarith only [hk1]) hl hr hright hu
  have hδL := hU.wideLeftSupportDeficit_mem ha0 hha (by linarith only [hk1]) hzk
    hl hr hleft hright haffine hv
  have hτ := wideLeftTiltPenalty_bounds ha0 hh (by linarith only [hk1])
    (wideLeftIntersection_mem ha0 hha hvv.1 hvv.2)
  have hIR := wideNearRightIntercept_eq (U := U) ha0 hha k v
  have hIL := wideNearLeftIntercept_eq U k u
  have hmid : 1 ≤ (u + v) / 2 := by linarith only [hm, ha, hh1]
  have hcrossR := wide_crossing_ge_apex hk (by linarith only [hk1])
    (show 1 ≤ nearDiagonalNorm k by linarith only [hNorm.1]) hmid
    (show wideNearRightIntercept U k ≤ 1 - nearDiagonalNorm k + k * v by
      linarith only [hIR, hδL.1, hτ.1])
  have hcrossL := wide_crossing_ge_apex (u := v) (v := u) hk (by linarith only [hk1])
    (show 1 ≤ nearDiagonalNorm k by linarith only [hNorm.1])
    (by linarith only [hmid])
    (show wideNearLeftIntercept U k ≤ 1 - nearDiagonalNorm k + k * u by
      linarith only [hIL, hδR.1])
  have hpoints := hU.wide_near_intercepts_lower ha0 hl hr hleft hright (k := k)
  refine ⟨hcrossR, ?_, ?_, ?_⟩
  · linarith only [hcrossL]
  · exact wide_peak_fits hk0 hk1 hksq hNorm.1.le hh hh1.le hah.le
      (capRoof_le_one hU.isCompact hU.inStrip a) hpoints.1
  · exact wide_peak_fits hk0 hk1 hksq hNorm.1.le hh hh1.le hah.le
      (capRoof_le_one hU.isCompact hU.inStrip (-a))
      (by linarith only [hpoints.2, hh])

end AmbidextrousSofa
