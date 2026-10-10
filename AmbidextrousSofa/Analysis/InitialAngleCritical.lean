module

public import AmbidextrousSofa.Analysis.InitialAngleRelaxation

@[expose] public section

/-!
# Exact clipping and integrals at the three-support critical point

The critical support parameters have explicitly ordered wall intersections.
Their delicate falling-wall versus terminal-floor comparison is derived
from the natural inset equation and the two preliminary width ranges.
These are local parameter identities, not an assumed optimization of the
finite-support relaxation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def initialAngleCriticalB (K d : ℝ) : ℝ := (K + d) / 2

def initialAngleCriticalU (K C k d : ℝ) : ℝ :=
  (1 - k) * C + K / 2 + k * d / 2

def initialAngleCriticalV (K C k d : ℝ) : ℝ :=
  (1 + k) * C + K / 2 - k * d / 2

def initialAngleCriticalP (C k d : ℝ) : ℝ := -k * (C - d / 2)

theorem initialAngle_inset_equation {k d s : ℝ}
    (hk : 0 < k) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1) :
    k * (1 - d ^ 2) = 2 * d := by
  have hsq := congrArg (fun t : ℝ => t ^ 2) hkd
  have hprod : k * (k * (1 - d ^ 2) - 2 * d) = 0 := by
    nlinarith only [hs2, hkd, hsq]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (ne_of_gt hk))

theorem initialAngle_inset_pos {k d s : ℝ}
    (hk : 0 < k) (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2)
    (hkd : k * d = s - 1) : 0 < d := by
  have hs1 : 1 < s := by
    apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hs0).mp
    nlinarith [sq_pos_of_pos hk]
  have hd : d = (s - 1) / k := by
    apply (eq_div_iff (ne_of_gt hk)).mpr
    nlinarith only [hkd]
  rw [hd]
  exact div_pos (sub_pos.mpr hs1) hk

theorem initialAngle_inset_lt_offset {k d : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) (hd : 0 < d)
    (hparam : k * (1 - d ^ 2) = 2 * d) : d < Real.sqrt 2 - 1 := by
  have hden : 0 < 1 - d ^ 2 := by
    by_contra h
    have hprod := mul_nonpos_of_nonneg_of_nonpos hk0.le (le_of_not_gt h)
    nlinarith only [hprod, hparam, hd]
  have hquad : d ^ 2 + 2 * d < 1 := by
    nlinarith only [hparam, mul_pos (show 0 < 1 - k by linarith) hden]
  have hK0 := initialAngle_offset_bounds.1
  have hK := initialAngle_offset_sq
  by_contra h
  have hle : Real.sqrt 2 - 1 ≤ d := le_of_not_gt h
  have hsq := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ d + (Real.sqrt 2 - 1) by linarith)
  nlinarith only [hK, hquad, hsq, hle]

theorem initialAngle_inset_lt_seven_twenty_fifths {k d : ℝ}
    (hk0 : 0 < k) (hk1 : k ≤ 3 / 5) (hd : 0 < d)
    (hparam : k * (1 - d ^ 2) = 2 * d) : d < (7 / 25 : ℝ) := by
  have hdK := initialAngle_inset_lt_offset hk0 (by linarith) hd hparam
  have hK1 := initialAngle_offset_bounds.2
  have hden : 0 ≤ 1 - d ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - d by linarith)
      (show 0 ≤ 1 + d by linarith)]
  have hprod := mul_nonneg (show 0 ≤ 3 / 5 - k by linarith) hden
  by_contra h
  have hle : (7 / 25 : ℝ) ≤ d := le_of_not_gt h
  have hsq := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ d + 7 / 25 by linarith)
  nlinarith only [hparam, hprod, hle, hsq]

/-- The exact identity responsible for the critical floor clipping. -/
theorem initialAngle_critical_gap {K C k d : ℝ}
    (hK : K ^ 2 + 2 * K = 1) (hparam : k * (1 - d ^ 2) = 2 * d)
    (hd : 0 ≤ d) :
    initialAngleCriticalU K C k d - K - (K - d) / 2 =
      (1 - k) * (C - 1 / 2) + (K - d) ^ 2 / (2 * (1 + d)) := by
  have hden : 0 < 2 * (1 + d) := by positivity
  have hmul :
      (initialAngleCriticalU K C k d - K - (K - d) / 2 -
        (1 - k) * (C - 1 / 2)) * (2 * (1 + d)) = (K - d) ^ 2 := by
    unfold initialAngleCriticalU
    nlinarith only [hK, hparam]
  have hdiv := (eq_div_iff (ne_of_gt hden)).mpr hmul
  linarith only [hdiv]

/-- Both remaining width ranges put the critical falling floor strictly
to the right of the terminal floor. -/
theorem initialAngle_critical_gap_pos {C k d s : ℝ}
    (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hwidth : (49 / 100 < C ∧ k ≤ 3 / 5) ∨ 1 / 2 ≤ C) :
    (Real.sqrt 2 - 1 - d) / 2 <
      initialAngleCriticalU (Real.sqrt 2 - 1) C k d - (Real.sqrt 2 - 1) := by
  let K := Real.sqrt (2 : ℝ) - 1
  have hk : 0 < k := by linarith
  have hm : 0 < 1 - k := by linarith
  have hd := initialAngle_inset_pos hk hs0 hs2 hkd
  have hparam := initialAngle_inset_equation hk hs2 hkd
  have hdK : d < K := initialAngle_inset_lt_offset hk (by linarith) hd hparam
  have hformula : initialAngleCriticalU K C k d - K - (K - d) / 2 =
      (1 - k) * (C - 1 / 2) + (K - d) ^ 2 / (2 * (1 + d)) :=
    initialAngle_critical_gap (C := C) initialAngle_offset_sq hparam hd.le
  have hden : 0 < 2 * (1 + d) := by positivity
  have hK0 : (41 / 100 : ℝ) < K := initialAngle_offset_bounds.1
  change (K - d) / 2 < initialAngleCriticalU K C k d - K
  rcases hwidth with ⟨hC, hk35⟩ | hC
  · have hd28 := initialAngle_inset_lt_seven_twenty_fifths hk hk35 hd hparam
    have hgap : (13 / 100 : ℝ) < K - d := by linarith
    have hgapSq := mul_pos (sub_pos.mpr hgap)
      (show 0 < K - d + 13 / 100 by linarith)
    have hquot : (169 / 25600 : ℝ) < (K - d) ^ 2 / (2 * (1 + d)) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith only [hgapSq, hd28]
    have hwidthTerm : -(1 / 160 : ℝ) < (1 - k) * (C - 1 / 2) := by
      have hmul := mul_lt_mul_of_pos_left
        (show -(1 / 100 : ℝ) < C - 1 / 2 by linarith) hm
      nlinarith only [hmul, hk0]
    linarith only [hformula, hquot, hwidthTerm]
  · have hwidthTerm : 0 ≤ (1 - k) * (C - 1 / 2) :=
      mul_nonneg hm.le (sub_nonneg.mpr hC)
    have hquot : 0 < (K - d) ^ 2 / (2 * (1 + d)) :=
      div_pos (sq_pos_of_pos (sub_pos.mpr hdK)) hden
    linarith only [hformula, hwidthTerm, hquot]

/-- Once the proved floor gap is supplied, every critical wall switch and
outer ramp lies strictly inside its stated interval. -/
theorem initialAngle_critical_clipping {K C k d : ℝ}
    (hK : 0 < K) (hk0 : 0 < k) (hk1 : k < 1) (hdK : d < K) (hKC : K < C)
    (hgap : (K - d) / 2 < initialAngleCriticalU K C k d - K) :
    initialAngleCriticalB K d < C ∧
    C < C + K / 2 ∧ C + K / 2 < 2 * C ∧
    -C < K / 2 - C ∧ K / 2 - C < initialAngleCriticalP C k d ∧
    initialAngleCriticalP C k d < 0 ∧ 0 < (K - d) / 2 ∧
    (K - d) / 2 < initialAngleCriticalU K C k d - K ∧
    initialAngleCriticalU K C k d - K < C ∧
    C < initialAngleCriticalV K C k d ∧ initialAngleCriticalV K C k d < 2 * C ∧
    initialAngleCriticalB K d < initialAngleCriticalU K C k d ∧
    initialAngleCriticalU K C k d <
      2 * (1 - k) * C + k * initialAngleCriticalB K d := by
  have hcharge := mul_pos hk0 (show 0 < C - d / 2 by linarith)
  have hsupport := mul_pos (show 0 < 1 - k by linarith)
    (show 0 < C - d / 2 by linarith)
  have hslack := mul_pos (show 0 < 1 - k by linarith)
    (show 0 < C - K / 2 by linarith)
  unfold initialAngleCriticalB initialAngleCriticalU initialAngleCriticalV
    initialAngleCriticalP at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem initialAngle_integral_affine (m c a b : ℝ) :
    (∫ x in a..b, m * x + c) = m * (b ^ 2 - a ^ 2) / 2 + c * (b - a) := by
  have hc : Continuous (fun x : ℝ => m * x) := by fun_prop
  rw [intervalIntegral.integral_add (hc.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Integration of the ordered terminal/rising/falling/floor pieces.
Every order hypothesis concerns an actual affine wall intersection. -/
theorem initialAngle_integral_three_walls_ordered {C k a c e l p : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hCl : -C ≤ l) (hlp : l ≤ p) (hpa : p ≤ a) (haC : a ≤ C)
    (hle : l ≤ e) (hea : e ≤ a)
    (hcross : (1 + k) * l = k * e - c) (hapex : a - c = 2 * p) :
    (∫ x in (-C)..C, max (max 0 (min (a - x) (c + x))) (k * (e - x))) =
      k * (e * (l + C) - (l ^ 2 - C ^ 2) / 2) +
        c * (p - l) + (p ^ 2 - l ^ 2) / 2 + (a - p) ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => max (max 0 (min (a - x) (c + x))) (k * (e - x))
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hleft : (∫ x in (-C)..l, f x) =
      k * (e * (l + C) - (l ^ 2 - C ^ 2) / 2) := by
    calc
      _ = ∫ x in (-C)..l, (-k) * x + k * e := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hCl]
        intro x hx
        have hcharge : 0 ≤ k * (e - x) :=
          mul_nonneg hk0 (by linarith [hx.2] : 0 ≤ e - x)
        have hline : c + x ≤ k * (e - x) := by
          nlinarith only [hcross, mul_nonneg (show 0 ≤ 1 + k by linarith)
            (show 0 ≤ l - x by linarith [hx.2])]
        have hmax : f x = k * (e - x) :=
          max_eq_right (max_le hcharge ((min_le_right _ _).trans hline))
        rw [hmax]
        ring
      _ = _ := by rw [initialAngle_integral_affine]; ring
  have hmiddle : (∫ x in l..p, f x) =
      c * (p - l) + (p ^ 2 - l ^ 2) / 2 := by
    calc
      _ = ∫ x in l..p, 1 * x + c := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hlp]
        intro x hx
        have hbase : 0 ≤ c + l := by
          nlinarith only [hcross, mul_nonneg hk0 (sub_nonneg.mpr hle)]
        have hnonneg : 0 ≤ c + x := by linarith [hx.1]
        have htent : c + x ≤ a - x := by linarith only [hapex, hx.2]
        have hcharge : k * (e - x) ≤ c + x := by
          nlinarith only [hcross, mul_nonneg (show 0 ≤ 1 + k by linarith)
            (show 0 ≤ x - l by linarith [hx.1])]
        change max (max 0 (min (a - x) (c + x))) (k * (e - x)) = _
        rw [min_eq_right htent, max_eq_right hnonneg, max_eq_left hcharge]
        ring
      _ = _ := by rw [initialAngle_integral_affine]; ring
  have hright : (∫ x in p..a, f x) = (a - p) ^ 2 / 2 := by
    calc
      _ = ∫ x in p..a, (-1) * x + a := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hpa]
        intro x hx
        have hnonneg : 0 ≤ a - x := sub_nonneg.mpr hx.2
        have htent : a - x ≤ c + x := by linarith only [hapex, hx.1]
        have hcharge : k * (e - x) ≤ a - x := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr hk1) hnonneg,
            mul_nonneg hk0 (sub_nonneg.mpr hea)]
        change max (max 0 (min (a - x) (c + x))) (k * (e - x)) = _
        rw [min_eq_left htent, max_eq_right hnonneg, max_eq_left hcharge]
        ring
      _ = _ := by rw [initialAngle_integral_affine]; ring
  have hzero : (∫ x in a..C, f x) = 0 := by
    calc
      _ = ∫ x in a..C, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le haC]
        intro x hx
        have htent : min (a - x) (c + x) ≤ 0 :=
          (min_le_left _ _).trans (sub_nonpos.mpr hx.1)
        have hcharge : k * (e - x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hk0 (by linarith [hx.1] : e - x ≤ 0)
        change max (max 0 (min (a - x) (c + x))) (k * (e - x)) = 0
        rw [max_eq_left htent, max_eq_left hcharge]
      _ = 0 := by simp
  change (∫ x in (-C)..C, f x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-C) l) (hc.intervalIntegrable l C),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable l p) (hc.intervalIntegrable p C),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable p a) (hc.intervalIntegrable a C),
    hleft, hmiddle, hright, hzero]
  ring

theorem initialAngle_critical_left_loss {K C k d : ℝ}
    (hK : 0 < K) (hk0 : 0 < k) (hk1 : k < 1) (hdK : d < K) (hKC : K < C)
    (hgap : (K - d) / 2 < initialAngleCriticalU K C k d - K) :
    initialAngleRampLoss C (initialAngleCriticalV K C k d) =
      (C - K / 2 - k * (C - d / 2)) ^ 2 / 2 := by
  rcases initialAngle_critical_clipping hK hk0 hk1 hdK hKC hgap with
    ⟨_, _, _, _, _, _, _, _, _, hvC, hv2, _, _⟩
  rw [initialAngleRampLoss_eq_square hvC.le hv2.le]
  unfold initialAngleCriticalV
  ring

theorem initialAngle_critical_right_loss {K C k d : ℝ}
    (hK : 0 < K) (hk0 : 0 < k) (hk1 : k < 1) (hdK : d < K) (hKC : K < C)
    (hgap : (K - d) / 2 < initialAngleCriticalU K C k d - K) :
    initialAngleRightLoss C k (initialAngleCriticalU K C k d) (initialAngleCriticalB K d) =
      k * (3 * C ^ 2 / 2 - C * initialAngleCriticalB K d) +
        (1 - k) * (C - K / 2) ^ 2 / 2 := by
  rcases initialAngle_critical_clipping hK hk0 hk1 hdK hKC hgap with
    ⟨hbC, hx0C, hx02C, _, _, _, _, _, _, _, _, hbu, _⟩
  have hx0 : (initialAngleCriticalU K C k d - k * initialAngleCriticalB K d) / (1 - k) =
      C + K / 2 := by
    apply (div_eq_iff (ne_of_gt (show 0 < 1 - k by linarith))).mpr
    unfold initialAngleCriticalU initialAngleCriticalB
    ring
  rw [initialAngleRightLoss_eq_ramps hk0.le hk1 hbu.le, hx0,
    initialAngleRampLoss_eq_affine (show 0 ≤ C by linarith) hbC.le,
    initialAngleRampLoss_eq_square hx0C.le hx02C.le]
  ring

theorem initialAngle_critical_niche_loss {K C k d : ℝ}
    (hK : 0 < K) (hk0 : 0 < k) (hk1 : k < 1) (hdK : d < K) (hKC : K < C)
    (hgap : (K - d) / 2 < initialAngleCriticalU K C k d - K) :
    initialAngleNicheLoss K C k d (initialAngleCriticalU K C k d)
      (initialAngleCriticalV K C k d) (initialAngleCriticalB K d) =
      (C - K / 2) ^ 2 - (k * (C - d / 2)) ^ 2 / 2 +
        K * (k * (C - d / 2)) / 2 + k * K ^ 2 / 8 := by
  rcases initialAngle_critical_clipping hK hk0 hk1 hdK hKC hgap with
    ⟨_, _, _, hCl, hlp, _, _, _, haC, _, _, _, _⟩
  have hpa : initialAngleCriticalP C k d ≤ initialAngleCriticalU K C k d - K := by
    unfold initialAngleCriticalP initialAngleCriticalU
    nlinarith only [hK, hKC]
  have hle : K / 2 - C ≤ initialAngleCriticalB K d - d := by
    unfold initialAngleCriticalB
    linarith
  have hea : initialAngleCriticalB K d - d ≤ initialAngleCriticalU K C k d - K := by
    unfold initialAngleCriticalB
    linarith only [hgap]
  have hcross : (1 + k) * (K / 2 - C) =
      k * (initialAngleCriticalB K d - d) - (initialAngleCriticalV K C k d - K) := by
    unfold initialAngleCriticalB initialAngleCriticalV
    ring
  have hapex : (initialAngleCriticalU K C k d - K) -
      (initialAngleCriticalV K C k d - K) = 2 * initialAngleCriticalP C k d := by
    unfold initialAngleCriticalU initialAngleCriticalV initialAngleCriticalP
    ring
  have h := initialAngle_integral_three_walls_ordered hk0.le hk1.le hCl.le hlp.le
    hpa haC.le hle hea hcross hapex
  calc
    _ = k * ((initialAngleCriticalB K d - d) * ((K / 2 - C) + C) -
        ((K / 2 - C) ^ 2 - C ^ 2) / 2) +
        (initialAngleCriticalV K C k d - K) * (initialAngleCriticalP C k d - (K / 2 - C)) +
        (initialAngleCriticalP C k d ^ 2 - (K / 2 - C) ^ 2) / 2 +
        ((initialAngleCriticalU K C k d - K) - initialAngleCriticalP C k d) ^ 2 / 2 := h
    _ = _ := by
      unfold initialAngleCriticalB initialAngleCriticalU initialAngleCriticalV initialAngleCriticalP
      ring

/-- The exact value of the integral relaxation at the clipped critical
supports. This is an evaluation, not a global maximization assertion. -/
theorem initialAngleRelaxation_critical_eq_stationary {K C k d : ℝ}
    (hK : 0 < K) (hk0 : 0 < k) (hk1 : k < 1) (hdK : d < K) (hKC : K < C)
    (hgap : (K - d) / 2 < initialAngleCriticalU K C k d - K) :
    initialAngleRelaxation K C k d (initialAngleCriticalU K C k d)
      (initialAngleCriticalV K C k d) (initialAngleCriticalB K d) =
        initialAngleStationaryValue K C k d := by
  unfold initialAngleRelaxation
  rw [initialAngle_critical_left_loss hK hk0 hk1 hdK hKC hgap,
    initialAngle_critical_right_loss hK hk0 hk1 hdK hKC hgap,
    initialAngle_critical_niche_loss hK hk0 hk1 hdK hKC hgap]
  unfold initialAngleStationaryValue initialAngleCriticalB
  ring

theorem initialAngleRelaxation_critical_eq_of_width_range {C k d s : ℝ}
    (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hwidth : (49 / 100 < C ∧ k ≤ 3 / 5) ∨ 1 / 2 ≤ C) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d
      (initialAngleCriticalU (Real.sqrt 2 - 1) C k d)
      (initialAngleCriticalV (Real.sqrt 2 - 1) C k d)
      (initialAngleCriticalB (Real.sqrt 2 - 1) d) =
        initialAngleStationaryValue (Real.sqrt 2 - 1) C k d := by
  have hk : 0 < k := by linarith
  have hd := initialAngle_inset_pos hk hs0 hs2 hkd
  have hdK := initialAngle_inset_lt_offset hk (by linarith) hd
    (initialAngle_inset_equation hk hs2 hkd)
  have hK0 := initialAngle_offset_bounds.1
  have hK1 := initialAngle_offset_bounds.2
  have hKC : Real.sqrt 2 - 1 < C := by
    rcases hwidth with ⟨hC, _⟩ | hC <;> linarith
  exact initialAngleRelaxation_critical_eq_stationary (by linarith) hk (by linarith)
    hdK hKC (initialAngle_critical_gap_pos hk0 hk1 hs0 hs2 hkd hwidth)

end AmbidextrousSofa
