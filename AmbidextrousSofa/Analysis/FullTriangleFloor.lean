module

public import AmbidextrousSofa.Analysis.WideNichePieces
public import AmbidextrousSofa.Analysis.AsymmetricTent

@[expose] public section

/-!
# Complete niche triangles with their positive-floor loss

The signed gain is a complete symmetric triangle. The area removed by
the zero floor is bounded pointwise by one asymmetric triangle: its two
slopes are the descending gain slope and the opposite baseline slope.
Integrating that triangle gives the exact loss coefficient, including
when the baseline zero lies outside the signed gain interval.
-/

noncomputable section

open Set MeasureTheory Filter

namespace AmbidextrousSofa

theorem positive_gain_sub_floor_loss_le {b s T n : ℝ}
    (hfloor : max b 0 ≤ n) (hwall : b + s ≤ n) (hsT : s ≤ T) :
    max s 0 - max (min (-b) T) 0 ≤ n - max b 0 := by
  simp only [max_def, min_def] at *
  split_ifs at * <;> linarith

def fullTriangleRightZero (k u B : ℝ) : ℝ := (B - u + k) / (1 + k)

def fullTriangleFloorCoefficient (k : ℝ) : ℝ := (1 + k) / (2 * (2 + k))

theorem fullTriangleFloorCoefficient_eq {k : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) :
    fullTriangleFloorCoefficient k = (1 - k) / 2 := by
  rw [fullTriangleFloorCoefficient, div_eq_div_iff (by positivity) two_ne_zero]
  linear_combination 2 * hksq

theorem integral_fullTriangle_gain {k u b B d A : ℝ} (hk : 0 < k)
    (hl : d ≤ wideCrossing k u b) (hr : fullTriangleRightZero k u B ≤ A) :
    (∫ x in d..A, max (min ((1 + k) * (x - wideCrossing k u b))
      ((1 + k) * (fullTriangleRightZero k u B - x))) 0) =
        (max (wideGain k u b B) 0) ^ 2 / (1 + k) := by
  have hR : 0 < 1 + k := by linarith
  have hw : fullTriangleRightZero k u B - wideCrossing k u b =
      2 * wideGain k u b B / (1 + k) := by
    unfold fullTriangleRightZero wideCrossing wideGain
    field_simp
    ring
  rw [integral_positive_asymmetric_tent_full hR hR hl hr, hw]
  rcases le_total 0 (wideGain k u b B) with hZ | hZ
  · rw [max_eq_left hZ, max_eq_left (by positivity)]
    field_simp
    ring
  · rw [max_eq_right hZ, max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) hR.le)]
    ring

/-- The actual positive niche keeps a complete signed triangle except
for a precisely bounded positive-floor loss. No order is imposed on the
baseline zero relative to the triangle's two endpoints. -/
theorem fullTriangle_niche_gain_integral {n : ℝ → ℝ} {A k u v b B : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hn : ∀ l r, IntervalIntegrable n volume l r)
    (hfloor : ∀ x, max (min (u - k - x) (v - k + x)) 0 ≤ n x)
    (hwall : ∀ x, min (b + k * x) (B - x / k) ≤ n x)
    (hd : (u - v) / 2 ≤ A)
    (hl : (u - v) / 2 ≤ wideCrossing k u b)
    (hr : fullTriangleRightZero k u B ≤ A) :
    (max (wideGain k u b B) 0) ^ 2 / (1 + k) -
        fullTriangleFloorCoefficient k *
          (max (fullTriangleRightZero k u B - (u - k)) 0) ^ 2 ≤
      ∫ x in ((u - v) / 2)..A,
        n x - max (min (u - k - x) (v - k + x)) 0 := by
  let T : ℝ → ℝ := fun x => max (min
    ((1 + k) * (x - wideCrossing k u b))
    ((1 + k) * (fullTriangleRightZero k u B - x))) 0
  let L : ℝ → ℝ := fun x => max (min
    (1 * (x - (u - k))) ((1 + k) * (fullTriangleRightZero k u B - x))) 0
  have hT : Continuous T := by fun_prop
  have hL : Continuous L := by fun_prop
  have hR : 0 < 1 + k := by linarith
  have hpoint : ∀ x ∈ Icc ((u - v) / 2) A,
      T x - L x ≤ n x - max (min (u - k - x) (v - k + x)) 0 := by
    intro x hx
    have hbase : min (u - k - x) (v - k + x) = u - k - x := min_eq_left (by linarith [hx.1])
    have hs : min (b + k * x) (B - x / k) - (u - k - x) = min ((1 + k) *
        (x - wideCrossing k u b)) ((1 + k) * (fullTriangleRightZero k u B - x)) := by
      rw [← min_sub_sub_right]
      congr 1
      · unfold wideCrossing
        field_simp
        ring
      · unfold fullTriangleRightZero
        field_simp
        linear_combination x * hksq
    simp only [T, L, hbase, one_mul, ← neg_sub (u - k) x]
    exact positive_gain_sub_floor_loss_le (hbase ▸ hfloor x) (by linarith [hwall x])
      (min_le_right _ _)
  have hmono := intervalIntegral.integral_mono_on (f := fun x => T x - L x) hd
    ((hT.sub hL).intervalIntegrable _ _)
    ((hn _ _).sub (Continuous.intervalIntegrable (by fun_prop) _ _)) hpoint
  rw [intervalIntegral.integral_sub (hT.intervalIntegrable _ _) (hL.intervalIntegrable _ _),
    integral_fullTriangle_gain hk hl hr] at hmono
  have hLI := (intervalIntegral.integral_mono_interval (f := L) (min_le_left _ (u - k)) hd
    (le_max_left _ (fullTriangleRightZero k u B)) (.of_forall fun x => le_max_right _ _)
    (hL.intervalIntegrable _ _)).trans_eq
    (integral_positive_asymmetric_tent_full one_pos hR (min_le_right _ _) (le_max_right _ _))
  rw [fullTriangleFloorCoefficient]
  linarith [show 1 * (1 + k) * (max (fullTriangleRightZero k u B - (u - k)) 0) ^ 2 /
    (2 * (1 + (1 + k))) = (1 + k) / (2 * (2 + k)) *
      (max (fullTriangleRightZero k u B - (u - k)) 0) ^ 2 by ring]

end AmbidextrousSofa
