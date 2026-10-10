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

theorem integral_positive_asymmetric_tent_le_full {s t l r A B : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hAB : A ≤ B) :
    (∫ x in A..B, max (min (s * (x - l)) (t * (r - x))) 0) ≤
      s * t * (max (r - l) 0) ^ 2 / (2 * (s + t)) := by
  have hc : Continuous (fun x : ℝ => max (min (s * (x - l)) (t * (r - x))) 0) := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_interval (min_le_left A l) hAB
    (le_max_left B r) (Eventually.of_forall (fun x => le_max_right
      (min (s * (x - l)) (t * (r - x))) 0))
    (hc.intervalIntegrable (min A l) (max B r))
  exact hmono.trans_eq (integral_positive_asymmetric_tent_full hs ht
    (min_le_right A l) (le_max_right B r))

theorem positive_gain_sub_floor_loss_le {b s T n : ℝ}
    (hfloor : max b 0 ≤ n) (hwall : b + s ≤ n) (hsT : s ≤ T) :
    max s 0 - max (min T (-b)) 0 ≤ n - max b 0 := by
  by_cases hs : s ≤ 0
  · rw [max_eq_right hs]
    linarith only [hfloor, le_max_right (min T (-b)) 0]
  · have hs0 : 0 ≤ s := (le_of_not_ge hs)
    rw [max_eq_left hs0]
    by_cases hb : 0 ≤ b
    · rw [max_eq_left hb]
      linarith only [hwall, le_max_right (min T (-b)) 0]
    · have hb0 : b ≤ 0 := le_of_not_ge hb
      rw [max_eq_right hb0]
      by_cases hT : T ≤ -b
      · rw [min_eq_left hT, max_eq_left (hs0.trans hsT)]
        have hn : 0 ≤ n := (le_max_right b 0).trans hfloor
        linarith only [hsT, hn]
      · rw [min_eq_right (le_of_not_ge hT), max_eq_left (neg_nonneg.mpr hb0)]
        linarith only [hwall]

def fullTriangleRightZero (k u B : ℝ) : ℝ := (B - u + k) / (1 + k)

def fullTriangleFloorCoefficient (k : ℝ) : ℝ := (1 + k) / (2 * (2 + k))

theorem fullTriangleFloorCoefficient_eq {k : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) :
    fullTriangleFloorCoefficient k = (1 - k) / 2 := by
  unfold fullTriangleFloorCoefficient
  apply (div_eq_iff (by positivity : 2 * (2 + k) ≠ 0)).mpr
  nlinarith only [hksq]

theorem fullTriangle_width_identity {k : ℝ} (hk : 0 < k) (u b B : ℝ) :
    (1 + k) * (fullTriangleRightZero k u B - wideCrossing k u b) =
      2 * wideGain k u b B := by
  unfold fullTriangleRightZero wideCrossing wideGain
  field_simp [(by linarith only [hk] : 1 + k ≠ 0)] <;> ring

theorem fullTriangle_gain_identity {k : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (u b B x : ℝ) :
    min (b + k * x) (B - x / k) - (u - k - x) =
      min ((1 + k) * (x - wideCrossing k u b))
        ((1 + k) * (fullTriangleRightZero k u B - x)) := by
  have hkR : 1 + k ≠ 0 := by linarith only [hk]
  have hi : 1 / k = k + 2 := by
    apply (div_eq_iff hk.ne').mpr
    nlinarith only [hksq]
  rw [← min_sub_sub_right]
  congr 1
  · unfold wideCrossing
    field_simp [hkR] <;> ring
  · unfold fullTriangleRightZero
    rw [div_eq_mul_inv, show k⁻¹ = k + 2 by simpa only [one_div] using hi]
    field_simp [hkR] <;> ring

theorem integral_fullTriangle_gain {k u b B d A : ℝ} (hk : 0 < k)
    (hl : d ≤ wideCrossing k u b) (hr : fullTriangleRightZero k u B ≤ A) :
    (∫ x in d..A, max (min ((1 + k) * (x - wideCrossing k u b))
      ((1 + k) * (fullTriangleRightZero k u B - x))) 0) =
        (max (wideGain k u b B) 0) ^ 2 / (1 + k) := by
  have hR : 0 < 1 + k := by linarith only [hk]
  rw [integral_positive_asymmetric_tent_full hR hR hl hr]
  have hw := fullTriangle_width_identity hk u b B
  by_cases hZ : 0 ≤ wideGain k u b B
  · have hwidth : 0 ≤ fullTriangleRightZero k u B - wideCrossing k u b := by
      apply nonneg_of_mul_nonneg_left (by linarith only [hw, hZ]) hR
    rw [max_eq_left hwidth, max_eq_left hZ]
    have hwidthEq : fullTriangleRightZero k u B - wideCrossing k u b =
        2 * wideGain k u b B / (1 + k) := by
      apply (eq_div_iff hR.ne').mpr
      nlinarith only [hw]
    rw [hwidthEq]
    field_simp [hR.ne'] <;> ring
  · have hwidth : fullTriangleRightZero k u B - wideCrossing k u b ≤ 0 := by
      apply nonpos_of_mul_nonpos_left (by linarith only [hw, le_of_not_ge hZ]) hR
    rw [max_eq_right hwidth, max_eq_right (le_of_not_ge hZ)]
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
    ((1 + k) * (fullTriangleRightZero k u B - x)) (x - (u - k))) 0
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hF : Continuous (fun x : ℝ => max (min (u - k - x) (v - k + x)) 0) := by
    fun_prop
  have hpoint : ∀ x ∈ Icc ((u - v) / 2) A,
      T x - L x ≤ n x - max (min (u - k - x) (v - k + x)) 0 := by
    intro x hx
    have hbase : min (u - k - x) (v - k + x) = u - k - x :=
      min_eq_left (by linarith only [hx.1])
    have hs := fullTriangle_gain_identity hk hksq u b B x
    have hw : (u - k - x) +
        min ((1 + k) * (x - wideCrossing k u b))
          ((1 + k) * (fullTriangleRightZero k u B - x)) ≤ n x := by
      linarith only [hwall x, hs]
    have hp := positive_gain_sub_floor_loss_le
      (by simpa only [hbase] using hfloor x) hw (min_le_right _ _)
    simpa only [T, L, hbase,
      show -(u - k - x) = x - (u - k) by ring] using hp
  have hmono := intervalIntegral.integral_mono_on hd
    ((hT.sub hL).intervalIntegrable _ _) ((hn _ _).sub (hF.intervalIntegrable _ _)) hpoint
  rw [intervalIntegral.integral_sub (hT.intervalIntegrable _ _)
    (hL.intervalIntegrable _ _)] at hmono
  have hTI : (∫ x in ((u - v) / 2)..A, T x) =
      (max (wideGain k u b B) 0) ^ 2 / (1 + k) := integral_fullTriangle_gain hk hl hr
  have hLI : (∫ x in ((u - v) / 2)..A, L x) ≤
      fullTriangleFloorCoefficient k *
        (max (fullTriangleRightZero k u B - (u - k)) 0) ^ 2 := by
    have h := integral_positive_asymmetric_tent_le_full
      (l := u - k) (r := fullTriangleRightZero k u B)
      (by norm_num : (0 : ℝ) < 1) (by linarith only [hk] : 0 < 1 + k) hd
    simpa only [L, one_mul, min_comm,
      show 1 + (1 + k) = 2 + k by ring, div_eq_mul_inv,
      fullTriangleFloorCoefficient, mul_assoc, mul_left_comm, mul_comm] using h
  linarith only [hmono, hTI, hLI]

end AmbidextrousSofa
