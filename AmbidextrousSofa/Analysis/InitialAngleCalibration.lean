module

public import AmbidextrousSofa.Analysis.InitialAngleCritical

@[expose] public section

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
  rcases le_total B A with hBA | hAB'
  · rw [max_eq_right (sub_nonpos.mpr hBA), max_eq_right (by linarith : -A ≤ 0), min_eq_right hBA]
    linarith [max_le_max (le_max_right 0 B) (le_refl L)]
  rw [max_eq_left (sub_nonneg.mpr hAB'), min_eq_left hAB']
  rcases le_total 0 A with hA | hA
  · rw [max_eq_right (neg_nonpos.mpr hA), max_eq_right hA]
    linarith [max_le (by linarith [le_max_left A L] : B ≤ max A L + (B - A))
      (by linarith [le_max_right A L] : L ≤ max A L + (B - A))]
  · rw [max_eq_left (neg_nonneg.mpr hA), max_eq_left hA]
    linarith [max_le (by linarith [le_max_left 0 L] : B ≤ B + max 0 L)
      (by linarith [le_max_right 0 L] : L ≤ B + max 0 L)]

/-- A ramp lies above the integral of its affine branch on any fixed
subinterval ending at the exterior endpoint. -/
theorem initialAngleRampLoss_tangent {C q : ℝ} (hCq : C ≤ q) (hq2 : q ≤ 2 * C)
    (z : ℝ) :
    ((2 * C) ^ 2 - q ^ 2) / 2 - z * (2 * C - q) ≤ initialAngleRampLoss C z := by
  have hramp : Continuous (fun x : ℝ => max (x - z) 0) := by fun_prop
  calc
    _ = ∫ x in q..(2 * C), 1 * x + -z := by rw [integral_affine]; ring
    _ ≤ ∫ x in q..(2 * C), max (x - z) 0 :=
      intervalIntegral.integral_mono hq2 (Continuous.intervalIntegrable (by fun_prop) _ _)
        (hramp.intervalIntegrable _ _) fun x => by linarith [le_max_left (x - z) 0]
    _ ≤ initialAngleRampLoss C z :=
      intervalIntegral.integral_mono_interval hCq hq2 le_rfl
        (ae_of_all _ fun x => le_max_right (x - z) 0) (hramp.intervalIntegrable _ _)

/-- The supporting plane of the right exterior loss at the critical
switch uses both clipped ramps, with no restriction on the moving switch. -/
theorem initialAngleRightLoss_affine_lower {K C k u b : ℝ}
    (hK0 : 0 ≤ K) (hK2 : K ≤ 2 * C) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbu : b ≤ u) :
    3 * C ^ 2 / 2 - C * u + K * (u - k * b - (1 - k) * C) / 2 -
      (1 - k) * K ^ 2 / 8 ≤ initialAngleRightLoss C k u b := by
  have hsplit : (1 - k) * ((u - k * b) / (1 - k)) = u - k * b :=
    mul_div_cancel₀ _ (by linarith)
  rw [initialAngleRightLoss_eq_ramps hk0 hk1 hbu]
  linarith [mul_le_mul_of_nonneg_left
      (initialAngleRampLoss_tangent (C := C) le_rfl (by linarith) b) hk0,
    mul_le_mul_of_nonneg_left (initialAngleRampLoss_tangent (C := C) (q := C + K / 2)
      (by linarith) (by linarith) ((u - k * b) / (1 - k))) (by linarith : 0 ≤ 1 - k),
    congrArg (C * ·) hsplit, congrArg (K * ·) hsplit]

/-- A fixed terminal/rising split gives an affine lower bound for their
whole maximum, whether or not the moving intersection stays in the window. -/
theorem initialAngle_V_integral_affine_lower {K C : ℝ}
    (hK0 : 0 ≤ K) (hK2 : K ≤ 2 * C) (k c e : ℝ) :
    2 * C * c + K * ((1 + k) * C - c + k * e) / 2 - (1 + k) * K ^ 2 / 8 ≤
      ∫ x in (-C)..C, max (c + x) (k * (e - x)) := by
  have hV : Continuous (fun x : ℝ => max (c + x) (k * (e - x))) := by fun_prop
  have hleft : (∫ x in (-C)..(K / 2 - C), -k * x + k * e) ≤
      ∫ x in (-C)..(K / 2 - C), max (c + x) (k * (e - x)) :=
    intervalIntegral.integral_mono (by linarith) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hV.intervalIntegrable _ _) fun x => by linarith [le_max_right (c + x) (k * (e - x))]
  have hright : (∫ x in (K / 2 - C)..C, 1 * x + c) ≤
      ∫ x in (K / 2 - C)..C, max (c + x) (k * (e - x)) :=
    intervalIntegral.integral_mono (by linarith) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hV.intervalIntegrable _ _) fun x => by linarith [le_max_left (c + x) (k * (e - x))]
  rw [integral_affine] at hleft hright
  rw [← intervalIntegral.integral_add_adjacent_intervals (hV.intervalIntegrable _ (K / 2 - C))
    (hV.intervalIntegrable _ _)]
  linarith

theorem initialAngle_integral_ramp_centered {C z : ℝ} (hz : z ∈ Icc (-C) C) :
    (∫ x in (-C)..C, max (x - z) 0) = (C - z) ^ 2 / 2 := by
  simp only [sub_eq_neg_add, integral_positive_ramp_add]
  rw [max_eq_left (by linarith [hz.2] : 0 ≤ -z + C),
    max_eq_right (by linarith [hz.1] : -z + -C ≤ 0)]
  ring

/-- The tent-apex loss and the exposed falling floor separate from the
rising/terminal maximum by two exact centered ramp integrals. -/
theorem initialAngle_niche_lower {K C k d u v b : ℝ} (hC : 0 ≤ C) (hsum : 2 * K ≤ u + v)
    (hp : (u - v) / 2 ∈ Icc (-C) C) :
    (∫ x in (-C)..C, max (v - K + x) (k * (b - d - x))) - (C - (u - v) / 2) ^ 2 +
      (∫ x in (-C)..C, max (x - (u - K)) 0) ≤ initialAngleNicheLoss K C k d u v b := by
  have hV : Continuous (fun x : ℝ => max (v - K + x) (k * (b - d - x))) := by fun_prop
  have hP : Continuous (fun x : ℝ => max (x - (u - v) / 2) 0) := by fun_prop
  have hA : Continuous (fun x : ℝ => max (x - (u - K)) 0) := by fun_prop
  have hmono := intervalIntegral.integral_mono (μ := volume) (by linarith : -C ≤ C)
    (((hV.fun_sub (hP.const_mul 2)).fun_add hA).intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop :
      Continuous fun x : ℝ => max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x))) _ _)
    fun x => by
      have h := initialAngle_wall_pointwise_lower
        (A := u - K - x) (B := v - K + x) (L := k * (b - d - x)) (by linarith)
      rw [show (v - K + x) - (u - K - x) = 2 * (x - (u - v) / 2) by ring,
        show -(u - K - x) = x - (u - K) by ring] at h
      linarith [mul_max_of_nonneg (x - (u - v) / 2) 0 zero_le_two]
  rw [intervalIntegral.integral_add ((hV.fun_sub (hP.const_mul 2)).intervalIntegrable _ _)
      (hA.intervalIntegrable _ _), intervalIntegral.integral_sub (hV.intervalIntegrable _ _)
      ((hP.const_mul 2).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    initialAngle_integral_ramp_centered hp] at hmono
  unfold initialAngleNicheLoss
  linarith

/-- The entire first region is calibrated by a single nonnegative square. -/
theorem initialAngleRelaxation_first_region_le {K C k d u v b : ℝ}
    (hK0 : 0 ≤ K) (hK2 : K ≤ 2 * C) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbu : b ≤ u) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C)
    (hsum : 2 * K ≤ u + v) (hp : (u - v) / 2 ∈ Icc (-C) C)
    (hu : u ≤ C + K) :
    initialAngleRelaxation K C k d u v b ≤
      initialAngleStationaryValue K C k d - (u + v - 2 * C - K) ^ 2 / 4 := by
  have hN := initialAngle_niche_lower (k := k) (d := d) (b := b) (by linarith) hsum hp
  rw [initialAngle_integral_ramp_centered (by constructor <;> linarith [hp.1])] at hN
  unfold initialAngleRelaxation initialAngleStationaryValue
  linarith [initialAngleRightLoss_affine_lower hK0 hK2 hk0 hk1 hbu,
    initialAngle_V_integral_affine_lower hK0 hK2 k (v - K) (b - d),
    initialAngleRampLoss_eq_square hv0 hv1]

theorem initialAngleRelaxation_le_exterior {C : ℝ} (hC : 0 ≤ C) (K k d u v b : ℝ) :
    initialAngleRelaxation K C k d u v b ≤
      2 * C - initialAngleRampLoss C u - initialAngleRampLoss C v := by
  unfold initialAngleRelaxation
  linarith [initialAngleRampLoss_le_rightLoss hC k u b, initialAngleNicheLoss_nonneg hC K k d u v b]

/-- An apex to the left of the whole window already loses enough exterior area. -/
theorem initialAngleRelaxation_le_two_thirds_of_left_apex {C u v : ℝ}
    (hC : 0 ≤ C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) (hapex : u - v ≤ -2 * C)
    (K k d b : ℝ) : initialAngleRelaxation K C k d u v b ≤ (2 / 3 : ℝ) := by
  linarith [initialAngleRelaxation_le_exterior hC K k d u v b,
    initialAngleRampLoss_eq_affine hC (show u ≤ C by linarith),
    initialAngleRampLoss_eq_square hv0 hv1, mul_nonneg hC (show 0 ≤ v - 2 * C - u by linarith),
    mul_nonneg (show 0 ≤ 2 * C - v by linarith) (show 0 ≤ 4 * C - v by linarith),
    sq_nonneg (3 * C - 2)]

/-- A nonpositive diagonal apex is also below `2/3`, including the narrow
widths on either side of `C=K`. -/
theorem initialAngleRelaxation_le_two_thirds_of_low_apex {K C u v : ℝ}
    (hC : 0 ≤ C) (hK0 : 0 ≤ K) (hK1 : K ≤ 5 / 12) (hK : K ^ 2 + 2 * K = 1)
    (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) (hsum : u + v ≤ 2 * K)
    (k d b : ℝ) : initialAngleRelaxation K C k d u v b ≤ (2 / 3 : ℝ) := by
  rcases le_total K (2 * C) with hK2 | hK2
  · have hext := initialAngleRelaxation_le_exterior hC K k d u v b
    rcases le_total u C with hu | hu
    · linarith [hext, initialAngleRampLoss_eq_affine hC hu,
        initialAngleRampLoss_eq_square hv0 hv1, mul_nonneg hC (show 0 ≤ 2 * K - u - v by linarith),
        hK, sq_nonneg (v - C), sq_nonneg (3 * C - 1 - K)]
    · have hCK : C ≤ K := by linarith
      linarith [hext, initialAngleRampLoss_tangent hCK hK2 u,
        initialAngleRampLoss_tangent hCK hK2 v,
        mul_nonneg (show 0 ≤ 2 * C - K by linarith) (show 0 ≤ 2 * K - u - v by linarith),
        mul_nonneg (sub_nonneg.mpr hCK) (show 0 ≤ 2 - 4 * C by linarith), hK, hK1]
  · linarith only [initialAngleRelaxation_le_twice_width hC K k d u v b, hK2, hK,
      mul_nonneg hK0 hK0]

/-- When the rising/terminal intersection is inside the window, its
maximum has an exact quadratic integral. -/
theorem initialAngle_V_integral_quadratic {C k c e : ℝ}
    (hk : -1 < k) (hY0 : 0 ≤ (1 + k) * C - c + k * e)
    (hY2 : (1 + k) * C - c + k * e ≤ 2 * (1 + k) * C) :
    (∫ x in (-C)..C, max (c + x) (k * (e - x))) =
      2 * C * c + ((1 + k) * C - c + k * e) ^ 2 / (2 * (1 + k)) := by
  have ht : 0 < 1 + k := by linarith
  obtain ⟨l, hsplit⟩ : ∃ l, (1 + k) * l = k * e - c :=
    ⟨(k * e - c) / (1 + k), mul_div_cancel₀ _ ht.ne'⟩
  have hl0 : -C ≤ l := le_of_mul_le_mul_left (by linarith) ht
  have hl1 : l ≤ C := le_of_mul_le_mul_left (by linarith) ht
  have hfun : (fun x : ℝ => max (c + x) (k * (e - x))) =
      fun x : ℝ => 1 * x + c + (1 + k) * max (l - x) 0 := by
    funext x
    rcases le_total x l with hxl | hlx
    · rw [max_eq_right (by linarith [mul_nonneg ht.le (sub_nonneg.mpr hxl)]),
        max_eq_left (sub_nonneg.mpr hxl)]
      linear_combination -hsplit
    · rw [max_eq_left (by linarith [mul_nonneg ht.le (sub_nonneg.mpr hlx)]),
        max_eq_right (sub_nonpos.mpr hlx)]
      ring
  rw [hfun, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    integral_affine, integral_positive_ramp_sub,
    max_eq_left (show 0 ≤ l - -C by linarith), max_eq_right (sub_nonpos.mpr hl1),
    show (1 + k) * C - c + k * e = (1 + k) * (C + l) by linear_combination -hsplit]
  field_simp
  ring

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
  have hsq : (2 * (1 - k) * C - u + k * b) ^ 2 / (2 * (1 - k)) =
      (1 - k) * (2 * C - (u - k * b) / (1 - k)) ^ 2 / 2 := by
    field_simp
    ring
  rw [initialAngleRightLoss_eq_ramps hk0 hk1 hbu, initialAngleRampLoss_eq_square hz0 hz1, hsq]
  linarith [mul_le_mul_of_nonneg_left
    (initialAngleRampLoss_tangent (C := C) le_rfl (by linarith) b) hk0]

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
  have hm : 1 - k ≠ 0 := by linarith
  have hp : 1 + k ≠ 0 := by linarith
  unfold initialAngleSecondRegionValue initialAngleStationaryValue
    initialAngleCriticalU initialAngleCriticalV initialAngleCriticalB
  field_simp
  ring

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
  have hz0 : C ≤ (u - k * b) / (1 - k) := (le_div_iff₀ hm).2 (by
    linarith [mul_nonneg hk0 (sub_nonneg.mpr hbu), mul_nonneg (by linarith : 0 ≤ u - C) hm.le])
  have hz1 : (u - k * b) / (1 - k) ≤ 2 * C := (div_le_iff₀ hm).2 (by linarith)
  have hp : (u - v) / 2 ∈ Icc (-C) C := by constructor <;> linarith
  have hN := initialAngle_niche_lower (K := K) (k := k) (d := d) (b := b) hC (by linarith) hp
  have hY2 : (1 + k) * C - (v - K) + k * (b - d) ≤ 2 * (1 + k) * C := by
    linarith [mul_le_mul_of_nonneg_left hb1 hk0, mul_nonneg hk0 hd0, mul_nonneg hm.le hC]
  have hV := initialAngle_V_integral_quadratic (by linarith) (by linarith) hY2
  rw [show (1 + k) * C - (v - K) + k * (b - d) = (1 + k) * C + K - v + k * (b - d) by ring] at hV
  have hupper : initialAngleRelaxation K C k d u v b ≤
      initialAngleSecondRegionValue K C k d u v b := by
    unfold initialAngleRelaxation initialAngleSecondRegionValue
    linarith [initialAngleRightLoss_quadratic_lower hC hk0 hk1 hbu hz0 hz1,
      initialAngleRampLoss_eq_square hv0 hv1, intervalIntegral.integral_nonneg_of_forall
        (μ := volume) (by linarith : -C ≤ C) fun x => le_max_right (x - (u - K)) 0]
  have ht : 0 ≤ C + K - initialAngleCriticalU K C k d := by
    unfold initialAngleCriticalU
    linarith [mul_nonneg hk0 (show 0 ≤ C - d / 2 by linarith)]
  rw [initialAngle_second_region_identity (by linarith) hk1] at hupper
  linarith [initialAngle_apex_variation_budget (ξ := u - initialAngleCriticalU K C k d)
      (η := v - initialAngleCriticalV K C k d) (ζ := b - initialAngleCriticalB K d)
      (by linarith) hk1,
    mul_le_mul_of_nonneg_left (sub_le_sub_right hu0 (initialAngleCriticalU K C k d)) ht,
    sq_nonneg (C + K - initialAngleCriticalU K C k d),
    sq_nonneg (v - initialAngleCriticalV K C k d)]

end AmbidextrousSofa
