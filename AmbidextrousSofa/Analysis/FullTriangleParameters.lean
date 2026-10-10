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
  have hN2 : nearDiagonalNorm k ^ 2 = 2 - 2 * k := by
    nlinarith only [nearDiagonalNorm_sq k, hksq]
  have hlow : (923 / 1000 : ℝ) * nearDiagonalNorm k < 1 := by
    by_contra hbad
    have h := mul_nonneg (show 0 ≤ 923 / 1000 * nearDiagonalNorm k - 1 by
      linarith only [le_of_not_gt hbad])
      (show 0 ≤ 923 / 1000 * nearDiagonalNorm k + 1 by positivity)
    nlinarith only [hN2, hk0, h]
  have hhigh : 1 < (231 / 250 : ℝ) * nearDiagonalNorm k := by
    by_contra hbad
    have h := mul_nonneg (show 0 ≤ 1 - 231 / 250 * nearDiagonalNorm k by
      linarith only [le_of_not_gt hbad])
      (show 0 ≤ 1 + 231 / 250 * nearDiagonalNorm k by positivity)
    nlinarith only [hN2, hk1, h]
  exact ⟨(lt_div_iff₀ hN).mpr hlow, (div_lt_iff₀ hN).mpr (by linarith only [hhigh])⟩

theorem fullTriangle_norm_identities {k : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) :
    1 / k = k + 2 ∧
      nearDiagonalNorm k / k = 2 * (1 + k) * fullTriangleCos k ∧
      nearDiagonalNorm k * (k + 3) = 4 * fullTriangleCos k := by
  have hN := nearDiagonalNorm_pos k
  have hN2 := nearDiagonalNorm_sq k
  have hi : 1 / k = k + 2 := by
    apply (div_eq_iff hk.ne').mpr
    nlinarith only [hksq]
  have hNk : nearDiagonalNorm k ^ 2 = 2 * (1 + k) * k := by
    nlinarith only [hN2, hksq]
  have hN3 : nearDiagonalNorm k ^ 2 * (k + 3) = 4 := by
    have hN2' : nearDiagonalNorm k ^ 2 = 2 - 2 * k := by nlinarith only [hN2, hksq]
    have h := congrArg (fun z : ℝ => z * (k + 3)) hN2'
    nlinarith only [h, hksq]
  refine ⟨hi, ?_, ?_⟩
  · unfold fullTriangleCos
    field_simp [hk.ne', hN.ne']
    nlinarith only [hNk]
  · unfold fullTriangleCos
    field_simp [hN.ne']
    nlinarith only [hN3]

theorem fullTriangle_outer_zero_le {a e k u : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (he : e ≤ 1 - (a - u)) :
    fullTriangleRightZero k u (wideEndpointIntercept a e k) ≤
      1 + a - 2 * fullTriangleCos k := by
  have hi := fullTriangle_norm_identities hk hksq
  have hR : 0 < 1 + k := by linarith only [hk]
  unfold fullTriangleRightZero wideEndpointIntercept
  apply (div_le_iff₀ hR).mpr
  have hdiv : (a - nearDiagonalNorm k) / k =
      a * (k + 2) - 2 * (1 + k) * fullTriangleCos k := by
    rw [sub_div, div_eq_mul_one_div a k, hi.1, hi.2.1]
  rw [hdiv]
  nlinarith only [he]

theorem fullTriangle_floor_loss_le_endpoint {a e k u : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (he : e ≤ 1 - (a - u)) :
    max (fullTriangleRightZero k u (wideEndpointIntercept a e k) - (u - k)) 0 ≤
      max (a - u - (2 * fullTriangleCos k - (1 + k))) 0 := by
  apply max_le_max _ le_rfl
  linarith only [fullTriangle_outer_zero_le hk hksq he]

theorem fullTriangle_crossing_after_apex {u v h k b : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hh : 0 ≤ h) (hM : 179 / 200 ≤ (u + v - h) / 2)
    (hb : b ≤ 1 - nearDiagonalNorm k + k * v - h) :
    (u - v + h) / 2 < wideCrossing k u b := by
  have hk : 0 < k := by linarith only [hk0]
  have hN := (wide_norm_rational_bounds
    (by linarith only [hk0]) hk1).1
  have hprod := mul_nonneg (show 0 ≤ 1 - k by linarith only [hk1])
    (show 0 ≤ (u + v + h) / 2 - 179 / 200 by linarith only [hM, hh])
  unfold wideCrossing
  apply (lt_div_iff₀ (by linarith only [hk] : 0 < 1 + k)).mpr
  nlinarith only [hprod, hb, hN, hk1]

theorem fullTriangle_reflected_crossing_after_apex {u v h k b : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hM : 179 / 200 ≤ (u + v - h) / 2)
    (hb : b ≤ 1 - nearDiagonalNorm k + k * u) :
    (v - h - u) / 2 < wideCrossing k (v - h) b := by
  have hk : 0 < k := by linarith only [hk0]
  have hN := (wide_norm_rational_bounds
    (by linarith only [hk0]) hk1).1
  have hprod := mul_nonneg (show 0 ≤ 1 - k by linarith only [hk1])
    (sub_nonneg.mpr hM)
  unfold wideCrossing
  apply (lt_div_iff₀ (by linarith only [hk] : 0 < 1 + k)).mpr
  nlinarith only [hprod, hb, hN, hk1]

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
  let d0 := 3 / 5 - (2 * fullTriangleCos k - (1 + k))
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  have hd0 : 1 / 8 < d0 := by dsimp [d0]; linarith only [hk0, hc.2]
  have hdR : 0 ≤ d0 - h / 4 := by linarith only [hd0, hh1]
  have hdL : 0 ≤ d0 + 3 * h / 4 := by linarith only [hd0, hh0]
  have hR := fullTriangle_floor_loss_le_endpoint hk hksq heR
  have hL := fullTriangle_floor_loss_le_endpoint (a := a) (e := eL) (u := v - h) hk hksq
    (by linarith only [heL])
  have hR' : max (fullTriangleRightZero k u (wideEndpointIntercept a eR k) - (u - k)) 0 ≤
      d0 - h / 4 := hR.trans (max_le (by dsimp [d0]; linarith only [hwR]) hdR)
  have hL' : max (fullTriangleRightZero k (v - h) (wideEndpointIntercept a eL k) -
      (v - h - k)) 0 ≤ d0 + 3 * h / 4 :=
    hL.trans (max_le (by dsimp [d0]; linarith only [hwL]) hdL)
  have hRsq := (sq_le_sq₀ (le_max_right _ _) hdR).mpr hR'
  have hLsq := (sq_le_sq₀ (le_max_right _ _) hdL).mpr hL'
  have hγ : 0 ≤ (1 - k) / 2 := by linarith only [hk1]
  rw [fullTriangleFloorCoefficient_eq hk hksq]
  exact mul_le_mul_of_nonneg_left (add_le_add hRsq hLsq) hγ

theorem fullTriangle_gain_sum {a eR eL h k u v bR bL δR δL : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hbR : bR = 1 - nearDiagonalNorm k + k * v - h - δL)
    (hbL : bL = 1 - nearDiagonalNorm k + k * u - δR)
    (hEP : 1 - h / 2 ≤ eR + eL) :
    fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k) ≤
      wideGain k u bR (wideEndpointIntercept a eR k) +
        wideGain k (v - h) bL (wideEndpointIntercept a eL k) + (δR + δL) / 2 := by
  have hi := fullTriangle_norm_identities hk hksq
  have hsum :
      wideGain k u bR (wideEndpointIntercept a eR k) +
        wideGain k (v - h) bL (wideEndpointIntercept a eL k) + (δR + δL) / 2 =
      (eR + eL) / 2 + (k + 2) * a + (k - 2) * ((u + v) / 2) +
        1 - 4 * fullTriangleCos k + 2 * k + h / 2 := by
    unfold wideGain wideEndpointIntercept
    rw [hbR, hbL]
    have hdiv : (a - nearDiagonalNorm k) / k = (k + 2) * a -
        nearDiagonalNorm k * (k + 2) := by
      rw [div_eq_mul_one_div, hi.1]
      ring
    rw [hdiv]
    have hN : nearDiagonalNorm k + nearDiagonalNorm k * (k + 2) =
        4 * fullTriangleCos k := by nlinarith only [hi.2.2]
    linarith only [hN]
  rw [hsum]
  unfold fullTriangleDemand
  linarith only [hEP]

end AmbidextrousSofa
