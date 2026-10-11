module

public import AmbidextrousSofa.Analysis.FullTriangleScalar
public import AmbidextrousSofa.Analysis.WideNicheGeometry

@[expose] public section

/-!
# Parameters of the actual three-angle niche comparison

Unnormalized support directions avoid any auxiliary lifted body. The
left diagonal parameter includes the actual middle height deficit, and
its nearby support is evaluated on the original cap. Every full niche
triangle and every floor-loss bound therefore uses original support and
endpoint data.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def fullTriangleCos (k : ℝ) : ℝ := 1 / nearDiagonalNorm k

theorem fullTriangleCos_bounds {k : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1) :
    923 / 1000 < fullTriangleCos k ∧ fullTriangleCos k < 231 / 250 := by
  have hN := nearDiagonalNorm_pos k
  have hN2 := nearDiagonalNorm_sq k
  rw [fullTriangleCos, lt_div_iff₀ hN, div_lt_iff₀ hN]
  constructor <;> nlinarith

theorem fullTriangle_norm_identities {k : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) :
    1 / k = k + 2 ∧
      nearDiagonalNorm k / k = 2 * (1 + k) * fullTriangleCos k ∧
      nearDiagonalNorm k * (k + 3) = 4 * fullTriangleCos k := by
  have hN := (nearDiagonalNorm_pos k).ne'
  have hN2 := nearDiagonalNorm_sq k
  rw [fullTriangleCos, mul_one_div, mul_one_div, div_eq_iff hk.ne', div_eq_div_iff hk.ne' hN,
    eq_div_iff hN]
  exact ⟨by linear_combination -hksq, by linear_combination hN2 - hksq,
    by linear_combination (k + 3) * hN2 + (k + 1) * hksq⟩

theorem fullTriangle_outer_zero_le {a e k u : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (he : e ≤ 1 - (a - u)) :
    fullTriangleRightZero k u (wideEndpointIntercept a e k) ≤
      1 + a - 2 * fullTriangleCos k := by
  have hi := fullTriangle_norm_identities hk hksq
  rw [fullTriangleRightZero, wideEndpointIntercept, div_le_iff₀ (by linarith), sub_div,
    div_eq_mul_one_div a k, hi.1, hi.2.1]
  linarith only [he]

theorem fullTriangle_floor_loss_le_endpoint {a e k u : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (he : e ≤ 1 - (a - u)) :
    max (fullTriangleRightZero k u (wideEndpointIntercept a e k) - (u - k)) 0 ≤
      max (a - u - (2 * fullTriangleCos k - (1 + k))) 0 :=
  max_le_max (by linarith only [fullTriangle_outer_zero_le hk hksq he]) le_rfl

theorem fullTriangle_crossing_after_apex {u v h k b : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hh : 0 ≤ h) (hM : 179 / 200 ≤ (u + v - h) / 2)
    (hb : b ≤ 1 - nearDiagonalNorm k + k * v - h) :
    (u - v + h) / 2 < wideCrossing k u b := by
  have hN := (wide_norm_rational_bounds (by linarith only [hk0]) hk1).1
  rw [wideCrossing, lt_div_iff₀ (by linarith only [hk0])]
  linarith only [mul_nonneg (by linarith only [hk1] : (0 : ℝ) ≤ 1 - k)
    (by linarith only [hM, hh] : 0 ≤ (u + v + h) / 2 - 179 / 200), hb, hN, hk1]

theorem fullTriangle_reflected_crossing_after_apex {u v h k b : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hM : 179 / 200 ≤ (u + v - h) / 2)
    (hb : b ≤ 1 - nearDiagonalNorm k + k * u) :
    (v - h - u) / 2 < wideCrossing k (v - h) b := by
  have hN := (wide_norm_rational_bounds (by linarith only [hk0]) hk1).1
  rw [wideCrossing, lt_div_iff₀ (by linarith only [hk0])]
  linarith only [mul_nonneg (by linarith only [hk1] : (0 : ℝ) ≤ 1 - k) (sub_nonneg.mpr hM),
    hb, hN, hk1]

theorem fullTriangle_loss_sum_le {a eR eL h k u v : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (heR : eR ≤ 1 - (a - u)) (heL : eL ≤ 1 - (a - v + h))
    (hwR : a - u ≤ 3 / 5 - h / 4) (hwL : a - v + h ≤ 3 / 5 + 3 * h / 4) :
    fullTriangleFloorCoefficient k *
      ((max (fullTriangleRightZero k u (wideEndpointIntercept a eR k) - (u - k)) 0) ^ 2 +
        (max (fullTriangleRightZero k (v - h) (wideEndpointIntercept a eL k) -
          (v - h - k)) 0) ^ 2) ≤ fullTriangleLoss h k (fullTriangleCos k) := by
  have hk : 0 < k := by linarith only [hk0]
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  have hR := fullTriangle_floor_loss_le_endpoint hk hksq heR
  have hL := fullTriangle_floor_loss_le_endpoint (a := a) (e := eL) (u := v - h) hk hksq
    (by linarith only [heL])
  rw [fullTriangleFloorCoefficient_eq hk hksq, fullTriangleLoss]
  gcongr
  · linarith only [hk1]
  · exact hR.trans (max_le (by linarith only [hwR]) (by linarith only [hc.2, hk0, hh1]))
  · exact hL.trans (max_le (by linarith only [hwL]) (by linarith only [hc.2, hk0, hh0]))

theorem fullTriangle_gain_sum {a eR eL h k u v bR bL δR δL : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hbR : bR = 1 - nearDiagonalNorm k + k * v - h - δL)
    (hbL : bL = 1 - nearDiagonalNorm k + k * u - δR)
    (hEP : 1 - h / 2 ≤ eR + eL) :
    fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k) ≤
      wideGain k u bR (wideEndpointIntercept a eR k) +
        wideGain k (v - h) bL (wideEndpointIntercept a eL k) + (δR + δL) / 2 := by
  have hi := fullTriangle_norm_identities hk hksq
  rw [fullTriangleDemand, wideGain, wideGain, wideEndpointIntercept, wideEndpointIntercept,
    div_eq_mul_one_div (a - _), hi.1, hbR, hbL]
  linarith only [hi.2.2, hEP]

end AmbidextrousSofa
