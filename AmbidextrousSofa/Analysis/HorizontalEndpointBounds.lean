module

public import AmbidextrousSofa.Analysis.NicheBoxBounds
public import AmbidextrousSofa.Analysis.EndpointPositivity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# Exact horizontal box-wall and endpoint bounds

The actual two-ray niche is bounded at both middle endpoints by
`1 - sqrt (1 - C^2)`. Endpoint stationarity then bounds both actual
axis heights and supplies one endpoint with the stronger quadratic
energy margin. The same box bounds give the exact initial angle at
which the first wall can become positive.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem horizontal_box_circle_bound {C s c : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hcircle : c ^ 2 + s ^ 2 = 1) :
    C * c + Real.sqrt (1 - C ^ 2) * s ≤ 1 := by
  have hid : (C * c + Real.sqrt (1 - C ^ 2) * s) ^ 2 +
      (C * s - Real.sqrt (1 - C ^ 2) * c) ^ 2 = 1 := by
    linear_combination (c ^ 2 + s ^ 2) * Real.sq_sqrt (show 0 ≤ 1 - C ^ 2 by nlinarith) + hcircle
  nlinarith [sq_nonneg (C * s - Real.sqrt (1 - C ^ 2) * c),
    sq_nonneg (C * c + Real.sqrt (1 - C ^ 2) * s - 1)]

theorem IsDownwardCap.middle_niche_le_box_height_of_box
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 1 - Real.sqrt (1 - C ^ 2) ∧
      sweptNiche U (Real.pi / 2) C ≤ 1 - Real.sqrt (1 - C ^ 2) := by
  have hH : 0 ≤ 1 - Real.sqrt (1 - C ^ 2) :=
    sub_nonneg.mpr (Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg C]))
  constructor <;> refine sweptNiche_le_of_forall (by positivity) hH fun t ht => ?_
  all_goals
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  · have := hU.support_companionNormal_le_centeredBox hbox hs.le hc.le
    have := horizontal_box_circle_bound (s := Real.cos t) (c := Real.sin t) hC0 hC1
      (Real.sin_sq_add_cos_sq t)
    refine (min_le_right _ _).trans ?_
    rw [secondWall, div_le_iff₀ hc]
    linarith
  · have := hU.support_unitNormal_le_centeredBox hbox hs.le hc.le
    have := horizontal_box_circle_bound (s := Real.sin t) (c := Real.cos t) hC0 hC1
      (Real.cos_sq_add_sin_sq t)
    refine (min_le_left _ _).trans ?_
    rw [firstWall, div_le_iff₀ hs]
    linarith

theorem IsDownwardCap.middle_niche_le_box_height_of_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 1 - Real.sqrt (1 - C ^ 2) ∧
      sweptNiche U (Real.pi / 2) C ≤ 1 - Real.sqrt (1 - C ^ 2) :=
  hU.middle_niche_le_box_height_of_box (hU.subset_centeredBox_of_endpoints hl hr) hC0 hC1

theorem IsFullCapMaximizer.horizontal_endpoint_laws
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    capRoof U (horizontalRight U) = 1 / 2 +
      (3 * sweptNiche U (Real.pi / 2) C - sweptNiche U (Real.pi / 2) (-C)) / 4 ∧
    capRoof U (horizontalLeft U) = 1 / 2 +
      (3 * sweptNiche U (Real.pi / 2) (-C) - sweptNiche U (Real.pi / 2) C) / 4 := by
  have hminus : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C := by
    rw [hl, hr]; ring
  have hplus : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C := by
    rw [hl, hr]; ring
  have hleft : capRoof U (-C) = 1 := hmiddle (-C) (by
    rw [middleHalfInterval, hminus, hplus]
    exact ⟨le_rfl, by linarith⟩)
  have hright : capRoof U C = 1 := hmiddle C (by
    rw [middleHalfInterval, hminus, hplus]
    exact ⟨by linarith, le_rfl⟩)
  obtain ⟨hR, hL⟩ := hU.endpoint_heights_eq_pressures_of_affine hheight
    ⟨0, 1, fun x hx => by simpa only [zero_mul, zero_add] using hmiddle x hx⟩
  simp only [capRightEndpointPressure, rightEndpointPressure, capLeftEndpointPressure,
    leftEndpointPressure, hminus, hplus, hleft, hright] at hR hL
  constructor <;> linarith only [hR, hL]

theorem IsFullCapMaximizer.horizontal_endpoint_heights_bounds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    (1 / 2 - (1 - Real.sqrt (1 - C ^ 2)) / 4 ≤ capRoof U (horizontalRight U) ∧
      capRoof U (horizontalRight U) ≤ 1 / 2 + 3 * (1 - Real.sqrt (1 - C ^ 2)) / 4) ∧
    (1 / 2 - (1 - Real.sqrt (1 - C ^ 2)) / 4 ≤ capRoof U (horizontalLeft U) ∧
      capRoof U (horizontalLeft U) ≤ 1 / 2 + 3 * (1 - Real.sqrt (1 - C ^ 2)) / 4) := by
  have he := hU.horizontal_endpoint_laws hl hr hC0 hheight hmiddle
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0 hC1
  have hnL0 := sweptNiche_nonneg U (Real.pi / 2) (-C)
  have hnR0 := sweptNiche_nonneg U (Real.pi / 2) C
  constructor <;> constructor <;> linarith [he.1, he.2, hn.1, hn.2]

theorem endpoint_product_one_ge_of_niche_bounds {x y H eR eL : ℝ}
    (hx0 : 0 ≤ x) (hxH : x ≤ H) (hy0 : 0 ≤ y) (hyH : y ≤ H)
    (heR : eR = 1 / 2 + (3 * x - y) / 4)
    (heL : eL = 1 / 2 + (3 * y - x) / 4) :
    (1 - H ^ 2) / 4 ≤ eR * (1 - eR) ∨
      (1 - H ^ 2) / 4 ≤ eL * (1 - eL) := by
  rcases le_total x y with hxy | hyx
  · left
    nlinarith [mul_nonneg (by linarith : 0 ≤ eR - 1 / 2 + H / 2)
      (by linarith : 0 ≤ H / 2 - (eR - 1 / 2))]
  · right
    nlinarith [mul_nonneg (by linarith : 0 ≤ eL - 1 / 2 + H / 2)
      (by linarith : 0 ≤ H / 2 - (eL - 1 / 2))]

theorem IsFullCapMaximizer.horizontal_endpoint_product_one_ge
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    (1 - (1 - Real.sqrt (1 - C ^ 2)) ^ 2) / 4 ≤
      capRoof U (horizontalRight U) * (1 - capRoof U (horizontalRight U)) ∨
    (1 - (1 - Real.sqrt (1 - C ^ 2)) ^ 2) / 4 ≤
      capRoof U (horizontalLeft U) * (1 - capRoof U (horizontalLeft U)) := by
  have he := hU.horizontal_endpoint_laws hl hr hC0 hheight hmiddle
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0 hC1
  exact endpoint_product_one_ge_of_niche_bounds
    (sweptNiche_nonneg U (Real.pi / 2) C) hn.2
    (sweptNiche_nonneg U (Real.pi / 2) (-C)) hn.1 he.1 he.2

theorem cos_horizontal_box_angle {C : ℝ} (hC0 : 0 ≤ C) :
    Real.cos (2 * Real.arctan ((1 - C) / (1 + C))) = 2 * C / (1 + C ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have hden : (1 + C) ≠ 0 := by positivity
  field_simp
  ring

theorem IsDownwardCap.firstWall_nonpos_before_horizontal_box_angle
    {U : Set Plane} (hU : IsDownwardCap U) {C t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (htb : t ≤ 2 * Real.arctan ((1 - C) / (1 + C))) :
    firstWall U t C ≤ 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hsupport := hU.support_unitNormal_le_centeredBox
    (hU.subset_centeredBox_of_endpoints hl hr) hs.le hc.le
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi ht.1.le
    (by linarith [Real.arctan_lt_pi_div_two ((1 - C) / (1 + C))]) htb
  rw [cos_horizontal_box_angle hC0, div_le_iff₀ (by positivity)] at hcos
  have hcC : C * Real.cos t ≤ 1 := by nlinarith only [Real.cos_le_one t, hC0, hC1]
  have hangle : Real.sin t + C * Real.cos t ≤ 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq t, mul_nonneg hc.le (sub_nonneg.mpr hcos), hcC]
  rw [firstWall, div_le_iff₀ hs]
  linarith only [hsupport, hangle]

end AmbidextrousSofa
