import AmbidextrousSofa.Analysis.InitialAngleCritical

/-!
# Direct calibration of the three-support relaxation

A pointwise inequality separates the sole concave tent switch from the
convex maximum of its rising line and the terminal wall. In the first
parameter region, the exact falling-floor ramp and two fixed support-line
integrals give a square remainder. In the second region, the exact
terminal and exterior switch quadratics pay for the tent apex. The two
bad-apex cases already lie below `2/3`. No general piecewise
differentiability or numerical optimization is used.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- A nonnegative tent apex permits a pointwise separation of the wall
maximum and the two compensating positive ramps. -/
theorem initialAngle_wall_pointwise_lower {A B L : ℝ} (hAB : 0 ≤ A + B) :
    max B L - max (B - A) 0 + max (-A) 0 ≤ max (max 0 (min A B)) L := by
  by_cases hBA : B ≤ A
  · have hA : 0 ≤ A := by linarith
    rw [max_eq_right (sub_nonpos.mpr hBA), max_eq_right (neg_nonpos.mpr hA),
      sub_zero, add_zero, min_eq_right hBA]
    exact max_le_max (le_max_right 0 B) le_rfl
  · have hAB' : A ≤ B := le_of_not_ge hBA
    have hB : 0 ≤ B := by linarith
    rw [max_eq_left (sub_nonneg.mpr hAB'), min_eq_left hAB']
    by_cases hA : 0 ≤ A
    · have hmax : max B L ≤ max A L + (B - A) :=
        max_le (by linarith [le_max_left A L]) (by linarith [le_max_right A L])
      rw [max_eq_right (neg_nonpos.mpr hA), max_eq_right hA]
      linarith only [hmax]
    · have hA' : A ≤ 0 := le_of_not_ge hA
      have hmax : max B L ≤ B + max 0 L :=
        max_le (by linarith [le_max_left 0 L]) (by linarith [le_max_right 0 L])
      rw [max_eq_left (neg_nonneg.mpr hA'), max_eq_left hA']
      linarith only [hmax]

/-- A ramp lies above the integral of its affine branch on any fixed
subinterval ending at the exterior endpoint. -/
theorem initialAngleRampLoss_tangent {C q : ℝ} (hCq : C ≤ q) (hq2 : q ≤ 2 * C)
    (z : ℝ) :
    ((2 * C) ^ 2 - q ^ 2) / 2 - z * (2 * C - q) ≤ initialAngleRampLoss C z := by
  have hline : Continuous (fun x : ℝ => 1 * x + (-z)) := by fun_prop
  have hramp : Continuous (fun x : ℝ => max (x - z) 0) := by fun_prop
  calc
    _ = ∫ x in q..(2 * C), 1 * x + (-z) := by
      rw [initialAngle_integral_affine]
      ring
    _ ≤ ∫ x in q..(2 * C), max (x - z) 0 := by
      apply intervalIntegral.integral_mono hq2
        (hline.intervalIntegrable q (2 * C)) (hramp.intervalIntegrable q (2 * C))
      intro x
      calc
        1 * x + (-z) = x - z := by ring
        _ ≤ _ := le_max_left _ _
    _ ≤ initialAngleRampLoss C z :=
      intervalIntegral.integral_mono_interval hCq hq2 le_rfl
        (ae_of_all _ fun x => le_max_right (x - z) 0)
        (hramp.intervalIntegrable C (2 * C))

/-- The supporting plane of the right exterior loss at the critical
switch uses both clipped ramps, with no restriction on the moving switch. -/
theorem initialAngleRightLoss_affine_lower {K C k u b : ℝ}
    (hK0 : 0 ≤ K) (hK2 : K ≤ 2 * C) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbu : b ≤ u) :
    3 * C ^ 2 / 2 - C * u + K * (u - k * b - (1 - k) * C) / 2 -
      (1 - k) * K ^ 2 / 8 ≤ initialAngleRightLoss C k u b := by
  let z := (u - k * b) / (1 - k)
  have hm : 0 < 1 - k := by linarith
  have hsplit : (1 - k) * z = u - k * b := mul_div_cancel₀ _ (ne_of_gt hm)
  have hsplitC := congrArg (fun t : ℝ => C * t) hsplit
  have hsplitK := congrArg (fun t : ℝ => K * t) hsplit
  have hfirst := mul_le_mul_of_nonneg_left
    (initialAngleRampLoss_tangent (C := C) le_rfl (by linarith) b) hk0
  have hsecond := mul_le_mul_of_nonneg_left
    (initialAngleRampLoss_tangent (C := C) (q := C + K / 2)
      (by linarith) (by linarith) z) hm.le
  have hQ : initialAngleRightLoss C k u b =
      k * initialAngleRampLoss C b + (1 - k) * initialAngleRampLoss C z :=
    initialAngleRightLoss_eq_ramps hk0 hk1 hbu
  nlinarith only [hfirst, hsecond, hQ, hsplitC, hsplitK]

/-- A fixed terminal/rising split gives an affine lower bound for their
whole maximum, whether or not the moving intersection stays in the window. -/
theorem initialAngle_V_integral_affine_lower {K C : ℝ}
    (hK0 : 0 ≤ K) (hK2 : K ≤ 2 * C) (k c e : ℝ) :
    2 * C * c + K * ((1 + k) * C - c + k * e) / 2 - (1 + k) * K ^ 2 / 8 ≤
      ∫ x in (-C)..C, max (c + x) (k * (e - x)) := by
  let l := K / 2 - C
  have hCl : -C ≤ l := by dsimp [l]; linarith
  have hlC : l ≤ C := by dsimp [l]; linarith
  have hV : Continuous (fun x : ℝ => max (c + x) (k * (e - x))) := by fun_prop
  have hL : Continuous (fun x : ℝ => (-k) * x + k * e) := by fun_prop
  have hR : Continuous (fun x : ℝ => 1 * x + c) := by fun_prop
  have hleft : (∫ x in (-C)..l, (-k) * x + k * e) ≤
      ∫ x in (-C)..l, max (c + x) (k * (e - x)) := by
    apply intervalIntegral.integral_mono hCl
      (hL.intervalIntegrable (-C) l) (hV.intervalIntegrable (-C) l)
    intro x
    calc
      (-k) * x + k * e = k * (e - x) := by ring
      _ ≤ _ := le_max_right _ _
  have hright : (∫ x in l..C, 1 * x + c) ≤
      ∫ x in l..C, max (c + x) (k * (e - x)) := by
    apply intervalIntegral.integral_mono hlC (hR.intervalIntegrable l C)
      (hV.intervalIntegrable l C)
    intro x
    calc
      1 * x + c = c + x := by ring
      _ ≤ _ := le_max_left _ _
  rw [initialAngle_integral_affine] at hleft hright
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hV.intervalIntegrable (-C) l) (hV.intervalIntegrable l C)
  dsimp [l] at hleft hright hadd
  nlinarith only [hleft, hright, hadd]

theorem initialAngle_integral_ramp_centered {C z : ℝ} (hz : z ∈ Icc (-C) C) :
    (∫ x in (-C)..C, max (x - z) 0) = (C - z) ^ 2 / 2 := by
  have hfun : (fun x : ℝ => max (x - z) 0) =
      (fun x : ℝ => max (-z + x) 0) := by
    funext x
    congr 1
    ring
  rw [hfun, integral_positive_ramp_add,
    show -z + C = C - z by ring,
    max_eq_left (sub_nonneg.mpr hz.2),
    max_eq_right (show -z + -C ≤ 0 by linarith [hz.1])]
  ring

/-- In the first region, the tent-apex loss and the exposed falling floor
have exact centered ramp integrals. -/
theorem initialAngle_niche_first_region_lower {K C k d u v b : ℝ}
    (hK0 : 0 ≤ K) (hK2 : K ≤ 2 * C) (hsum : 2 * K ≤ u + v)
    (hp : (u - v) / 2 ∈ Icc (-C) C) (hu : u ≤ C + K) :
    2 * C * (v - K) + K * ((1 + k) * C + K - v + k * (b - d)) / 2 -
      (1 + k) * K ^ 2 / 8 - (C - (u - v) / 2) ^ 2 +
        (C - u + K) ^ 2 / 2 ≤ initialAngleNicheLoss K C k d u v b := by
  have ha : u - K ∈ Icc (-C) C := by constructor <;> linarith [hp.1]
  have hV : Continuous (fun x : ℝ => max (v - K + x) (k * (b - d - x))) := by
    fun_prop
  have hP : Continuous (fun x : ℝ => max (x - (u - v) / 2) 0) := by fun_prop
  have hA : Continuous (fun x : ℝ => max (x - (u - K)) 0) := by fun_prop
  have hN : Continuous (fun x : ℝ =>
      max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x))) := by fun_prop
  have hmono : (∫ x in (-C)..C,
      max (v - K + x) (k * (b - d - x)) -
        2 * max (x - (u - v) / 2) 0 + max (x - (u - K)) 0) ≤
      initialAngleNicheLoss K C k d u v b := by
    apply intervalIntegral.integral_mono (by linarith)
      (((hV.sub (hP.const_mul 2)).add hA).intervalIntegrable (-C) C)
      (hN.intervalIntegrable (-C) C)
    intro x
    have h := initialAngle_wall_pointwise_lower
      (A := u - K - x) (B := v - K + x) (L := k * (b - d - x)) (by linarith)
    have hscale : max (2 * (x - (u - v) / 2)) 0 =
        2 * max (x - (u - v) / 2) 0 := by
      simpa only [mul_zero] using
        (mul_max_of_nonneg (x - (u - v) / 2) 0 (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [show (v - K + x) - (u - K - x) = 2 * (x - (u - v) / 2) by ring,
      hscale, show -(u - K - x) = x - (u - K) by ring] at h
    exact h
  rw [intervalIntegral.integral_add
      ((hV.sub (hP.const_mul 2)).intervalIntegrable (-C) C) (hA.intervalIntegrable (-C) C),
    intervalIntegral.integral_sub (hV.intervalIntegrable (-C) C)
      ((hP.const_mul 2).intervalIntegrable (-C) C),
    intervalIntegral.integral_const_mul, initialAngle_integral_ramp_centered hp,
    initialAngle_integral_ramp_centered ha] at hmono
  have hVbound := initialAngle_V_integral_affine_lower hK0 hK2 k (v - K) (b - d)
  nlinarith only [hmono, hVbound]

/-- The entire first region is calibrated by a single nonnegative square. -/
theorem initialAngleRelaxation_first_region_le {K C k d u v b : ℝ}
    (hK0 : 0 ≤ K) (hK2 : K ≤ 2 * C) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbu : b ≤ u) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C)
    (hsum : 2 * K ≤ u + v) (hp : (u - v) / 2 ∈ Icc (-C) C)
    (hu : u ≤ C + K) :
    initialAngleRelaxation K C k d u v b ≤
      initialAngleStationaryValue K C k d - (u + v - 2 * C - K) ^ 2 / 4 := by
  have hQ := initialAngleRightLoss_affine_lower hK0 hK2 hk0 hk1 hbu
  have hN := initialAngle_niche_first_region_lower hK0 hK2 hsum hp hu
  have hleft := initialAngleRampLoss_eq_square hv0 hv1
  unfold initialAngleRelaxation initialAngleStationaryValue
  nlinarith only [hQ, hN, hleft]

theorem initialAngleRelaxation_le_exterior {C : ℝ} (hC : 0 ≤ C) (K k d u v b : ℝ) :
    initialAngleRelaxation K C k d u v b ≤
      2 * C - initialAngleRampLoss C u - initialAngleRampLoss C v := by
  have hQ := initialAngleRampLoss_le_rightLoss hC k u b
  have hN := initialAngleNicheLoss_nonneg hC K k d u v b
  unfold initialAngleRelaxation
  linarith

/-- An apex to the left of the whole window already loses enough exterior area. -/
theorem initialAngleRelaxation_le_two_thirds_of_left_apex {C u v : ℝ}
    (hC : 0 ≤ C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) (hapex : u - v ≤ -2 * C)
    (K k d b : ℝ) : initialAngleRelaxation K C k d u v b ≤ (2 / 3 : ℝ) := by
  have hext := initialAngleRelaxation_le_exterior hC K k d u v b
  have hgu := initialAngleRampLoss_eq_affine hC (show u ≤ C by linarith)
  have hgv := initialAngleRampLoss_eq_square hv0 hv1
  have hscale := mul_nonneg hC (show 0 ≤ v - 2 * C - u by linarith)
  have hprod := mul_nonneg (show 0 ≤ 2 * C - v by linarith)
    (show 0 ≤ 4 * C - v by linarith)
  nlinarith only [hext, hgu, hgv, hscale, hprod, sq_nonneg (3 * C - 2)]

/-- A nonpositive diagonal apex is also below `2/3`, including the narrow
widths on either side of `C=K`. -/
theorem initialAngleRelaxation_le_two_thirds_of_low_apex {K C u v : ℝ}
    (hC : 0 ≤ C) (hK0 : 0 ≤ K) (hK1 : K ≤ 5 / 12) (hK : K ^ 2 + 2 * K = 1)
    (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) (hsum : u + v ≤ 2 * K)
    (k d b : ℝ) : initialAngleRelaxation K C k d u v b ≤ (2 / 3 : ℝ) := by
  by_cases hK2 : K ≤ 2 * C
  · have hext := initialAngleRelaxation_le_exterior hC K k d u v b
    by_cases hu : u ≤ C
    · have hgu := initialAngleRampLoss_eq_affine hC hu
      have hgv := initialAngleRampLoss_eq_square hv0 hv1
      have hscale := mul_nonneg hC (show 0 ≤ 2 * K - u - v by linarith)
      nlinarith only [hext, hgu, hgv, hscale, hK,
        sq_nonneg (v - C), sq_nonneg (3 * C - 1 - K)]
    · have hCK : C ≤ K := by linarith [lt_of_not_ge hu]
      have hgu := initialAngleRampLoss_tangent hCK hK2 u
      have hgv := initialAngleRampLoss_tangent hCK hK2 v
      have hscale := mul_nonneg (show 0 ≤ 2 * C - K by linarith)
        (show 0 ≤ 2 * K - u - v by linarith)
      have hend := mul_nonneg (sub_nonneg.mpr hCK)
        (show 0 ≤ 2 - 4 * C by linarith)
      nlinarith only [hext, hgu, hgv, hscale, hend, hK, hK1]
  · have htrivial := initialAngleRelaxation_le_twice_width hC K k d u v b
    linarith [lt_of_not_ge hK2]

/-- When the rising/terminal intersection is inside the window, its
maximum has an exact quadratic integral. -/
theorem initialAngle_V_integral_quadratic {C k c e : ℝ}
    (hk : -1 < k) (hY0 : 0 ≤ (1 + k) * C - c + k * e)
    (hY2 : (1 + k) * C - c + k * e ≤ 2 * (1 + k) * C) :
    (∫ x in (-C)..C, max (c + x) (k * (e - x))) =
      2 * C * c + ((1 + k) * C - c + k * e) ^ 2 / (2 * (1 + k)) := by
  let l := (k * e - c) / (1 + k)
  have ht : 0 < 1 + k := by linarith
  have hsplit : (1 + k) * l = k * e - c := mul_div_cancel₀ _ (ne_of_gt ht)
  have hl0 : -C ≤ l := by
    apply (le_div_iff₀ ht).2
    nlinarith only [hY0]
  have hl1 : l ≤ C := by
    apply (div_le_iff₀ ht).2
    nlinarith only [hY2]
  have hfun : (fun x : ℝ => max (c + x) (k * (e - x))) =
      (fun x : ℝ => 1 * x + c + (1 + k) * max (l - x) 0) := by
    funext x
    by_cases hxl : x ≤ l
    · have hlines : c + x ≤ k * (e - x) := by
        nlinarith only [hsplit, mul_nonneg ht.le (sub_nonneg.mpr hxl)]
      rw [max_eq_right hlines, max_eq_left (sub_nonneg.mpr hxl)]
      nlinarith only [hsplit]
    · have hlx : l ≤ x := le_of_not_ge hxl
      have hlines : k * (e - x) ≤ c + x := by
        nlinarith only [hsplit, mul_nonneg ht.le (sub_nonneg.mpr hlx)]
      rw [max_eq_left hlines, max_eq_right (sub_nonpos.mpr hlx)]
      ring
  have hline : Continuous (fun x : ℝ => 1 * x + c) := by fun_prop
  have hramp : Continuous (fun x : ℝ => (1 + k) * max (l - x) 0) := by fun_prop
  rw [hfun, intervalIntegral.integral_add (hline.intervalIntegrable (-C) C)
      (hramp.intervalIntegrable (-C) C), intervalIntegral.integral_const_mul,
    initialAngle_integral_affine, integral_positive_ramp_sub,
    max_eq_left (show 0 ≤ l - -C by linarith),
    max_eq_right (sub_nonpos.mpr hl1)]
  dsimp [l]
  field_simp [ne_of_gt ht] <;> ring

/-- Dropping the nonnegative falling-floor ramp gives the second-region
niche lower bound, retaining its exact rising/terminal switch. -/
theorem initialAngle_niche_second_region_lower {K C k d u v b : ℝ}
    (hC : 0 ≤ C) (hk : -1 < k) (hsum : 2 * K ≤ u + v)
    (hp : (u - v) / 2 ∈ Icc (-C) C)
    (hY0 : 0 ≤ (1 + k) * C + K - v + k * (b - d))
    (hY2 : (1 + k) * C + K - v + k * (b - d) ≤ 2 * (1 + k) * C) :
    2 * C * (v - K) + ((1 + k) * C + K - v + k * (b - d)) ^ 2 /
      (2 * (1 + k)) - (C - (u - v) / 2) ^ 2 ≤
        initialAngleNicheLoss K C k d u v b := by
  have hV : Continuous (fun x : ℝ => max (v - K + x) (k * (b - d - x))) := by
    fun_prop
  have hP : Continuous (fun x : ℝ => max (x - (u - v) / 2) 0) := by fun_prop
  have hN : Continuous (fun x : ℝ =>
      max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x))) := by fun_prop
  have hmono : (∫ x in (-C)..C,
      max (v - K + x) (k * (b - d - x)) - 2 * max (x - (u - v) / 2) 0) ≤
      initialAngleNicheLoss K C k d u v b := by
    apply intervalIntegral.integral_mono (by linarith)
      ((hV.sub (hP.const_mul 2)).intervalIntegrable (-C) C)
      (hN.intervalIntegrable (-C) C)
    intro x
    have h := initialAngle_wall_pointwise_lower
      (A := u - K - x) (B := v - K + x) (L := k * (b - d - x)) (by linarith)
    have hscale : max (2 * (x - (u - v) / 2)) 0 =
        2 * max (x - (u - v) / 2) 0 := by
      simpa only [mul_zero] using
        (mul_max_of_nonneg (x - (u - v) / 2) 0 (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [show (v - K + x) - (u - K - x) = 2 * (x - (u - v) / 2) by ring,
      hscale] at h
    linarith only [h, le_max_right (-(u - K - x)) 0]
  rw [intervalIntegral.integral_sub (hV.intervalIntegrable (-C) C)
      ((hP.const_mul 2).intervalIntegrable (-C) C),
    intervalIntegral.integral_const_mul, initialAngle_integral_ramp_centered hp] at hmono
  have hVexact := initialAngle_V_integral_quadratic (C := C) (c := v - K)
    (e := b - d) hk (by nlinarith only [hY0]) (by nlinarith only [hY2])
  nlinarith only [hmono, hVexact]

/-- The exterior moving switch supplies its full quadratic whenever the
support compatibility places it inside the exterior window. -/
theorem initialAngleRightLoss_quadratic_lower {C k u b : ℝ}
    (hC : 0 ≤ C) (hk0 : 0 ≤ k) (hk1 : k < 1) (hbu : b ≤ u)
    (hz0 : C ≤ (u - k * b) / (1 - k))
    (hz1 : (u - k * b) / (1 - k) ≤ 2 * C) :
    k * (3 * C ^ 2 / 2 - C * b) +
      (2 * (1 - k) * C - u + k * b) ^ 2 / (2 * (1 - k)) ≤
        initialAngleRightLoss C k u b := by
  have hm : 0 < 1 - k := by linarith
  have hfirst := mul_le_mul_of_nonneg_left
    (initialAngleRampLoss_tangent (C := C) le_rfl (by linarith) b) hk0
  rw [initialAngleRightLoss_eq_ramps hk0 hk1 hbu,
    initialAngleRampLoss_eq_square hz0 hz1]
  calc
    _ = k * (3 * C ^ 2 / 2 - C * b) +
        (1 - k) * (2 * C - (u - k * b) / (1 - k)) ^ 2 / 2 := by
      field_simp [ne_of_gt hm] <;> ring
    _ ≤ _ := by nlinarith only [hfirst]

/-- The comparison expression obtained from the exact second-region
wall switch and the exterior support switch. -/
def initialAngleSecondRegionValue (K C k d u v b : ℝ) : ℝ :=
  2 * C - (2 * C - v) ^ 2 / 2 - k * (3 * C ^ 2 / 2 - C * b) -
    (2 * (1 - k) * C - u + k * b) ^ 2 / (2 * (1 - k)) -
    2 * C * (v - K) - ((1 + k) * C + K - v + k * (b - d)) ^ 2 /
      (2 * (1 + k)) + (C - (u - v) / 2) ^ 2

/-- The exact translated quadratic at the common critical parameters. -/
theorem initialAngle_second_region_identity {K C k d u v b : ℝ}
    (hk0 : -1 < k) (hk1 : k < 1) :
    initialAngleSecondRegionValue K C k d u v b =
      initialAngleStationaryValue K C k d +
        (C + K - initialAngleCriticalU K C k d) ^ 2 / 2 -
        (C + K - initialAngleCriticalU K C k d) * (u - initialAngleCriticalU K C k d) -
        (((u - initialAngleCriticalU K C k d) - k * (b - initialAngleCriticalB K d)) ^ 2 /
            (1 - k) +
          ((v - initialAngleCriticalV K C k d) - k * (b - initialAngleCriticalB K d)) ^ 2 /
            (1 + k) + (v - initialAngleCriticalV K C k d) ^ 2 -
          ((u - initialAngleCriticalU K C k d) -
            (v - initialAngleCriticalV K C k d)) ^ 2 / 2) / 2 := by
  unfold initialAngleSecondRegionValue initialAngleStationaryValue
    initialAngleCriticalU initialAngleCriticalV initialAngleCriticalB
  field_simp [ne_of_gt (show 0 < 1 - k by linarith),
    ne_of_gt (show 0 < 1 + k by linarith)] <;> ring

/-- In the second region beyond the first, the two switch quadratics pay
the whole tent-apex variation. All window positions follow from the
ordinary support compatibility inequalities. -/
theorem initialAngleRelaxation_second_region_le {K C k d u v b : ℝ}
    (hK0 : 0 ≤ K) (hKC : K ≤ C) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hd0 : 0 ≤ d) (hdC : d ≤ 2 * C) (hbu : b ≤ u)
    (hu0 : C + K ≤ u) (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C)
    (hb1 : b ≤ 2 * C) (hcompat : u ≤ 2 * (1 - k) * C + k * b)
    (hY0 : 0 ≤ (1 + k) * C + K - v + k * (b - d)) :
    initialAngleRelaxation K C k d u v b ≤ initialAngleStationaryValue K C k d := by
  have hC : 0 ≤ C := hK0.trans hKC
  have hm : 0 < 1 - k := by linarith
  have hkneg : -1 < k := by linarith
  have huz : u ≤ (u - k * b) / (1 - k) := by
    apply (le_div_iff₀ hm).2
    nlinarith only [mul_nonneg hk0 (sub_nonneg.mpr hbu)]
  have hz0 : C ≤ (u - k * b) / (1 - k) := (by linarith : C ≤ u).trans huz
  have hz1 : (u - k * b) / (1 - k) ≤ 2 * C := by
    apply (div_le_iff₀ hm).2
    nlinarith only [hcompat]
  have hp : (u - v) / 2 ∈ Icc (-C) C := by constructor <;> linarith
  have hsum : 2 * K ≤ u + v := by linarith
  have hY2 : (1 + k) * C + K - v + k * (b - d) ≤ 2 * (1 + k) * C := by
    nlinarith only [hKC, hv0, mul_le_mul_of_nonneg_left hb1 hk0,
      mul_nonneg hk0 hd0, mul_nonneg hm.le hC]
  have hQ := initialAngleRightLoss_quadratic_lower hC hk0 hk1 hbu hz0 hz1
  have hN := initialAngle_niche_second_region_lower hC hkneg hsum hp hY0 hY2
  have hleft := initialAngleRampLoss_eq_square hv0 hv1
  have hupper : initialAngleRelaxation K C k d u v b ≤
      initialAngleSecondRegionValue K C k d u v b := by
    unfold initialAngleRelaxation initialAngleSecondRegionValue
    nlinarith only [hQ, hN, hleft]
  let t := C + K - initialAngleCriticalU K C k d
  let ξ := u - initialAngleCriticalU K C k d
  let η := v - initialAngleCriticalV K C k d
  let ζ := b - initialAngleCriticalB K d
  have ht : 0 ≤ t := by
    dsimp [t, initialAngleCriticalU]
    nlinarith only [hK0, mul_nonneg hk0 (show 0 ≤ C - d / 2 by linarith)]
  have htξ : t ≤ ξ := by dsimp [t, ξ]; linarith only [hu0]
  have hbudget := initialAngle_apex_variation_budget (ξ := ξ) (η := η) (ζ := ζ)
    hkneg hk1
  have hidentity : initialAngleSecondRegionValue K C k d u v b =
      initialAngleStationaryValue K C k d + t ^ 2 / 2 - t * ξ -
        ((ξ - k * ζ) ^ 2 / (1 - k) + (η - k * ζ) ^ 2 / (1 + k) +
          η ^ 2 - (ξ - η) ^ 2 / 2) / 2 :=
    initialAngle_second_region_identity hkneg hk1
  nlinarith only [hupper, hidentity, hbudget, mul_le_mul_of_nonneg_left htξ ht,
    sq_nonneg t, sq_nonneg η]

end AmbidextrousSofa
