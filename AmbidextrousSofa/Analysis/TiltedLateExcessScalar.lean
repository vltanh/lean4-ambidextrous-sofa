module

public import AmbidextrousSofa.Analysis.ProperExcessScalar
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Exact late-excess estimates for the tilted first wing

Compare the tilted floor energy with the zero-tilt trajectory. Tilt
delays the first zero by at most its height, but shortens the subsequent
excess by at least that height. The two effects cancel, and the entire
range inherits the zero-tilt stopping bound.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

/-- The strict endpoint-angle margin follows from a quadratic cosine
bound at the half-angle and the exact double-angle identity. -/
theorem cos_eleven_fifteenths_gt_thirty_seven_fiftieths :
    37 / 50 < Real.cos (11 / 15 : ℝ) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := (11 / 30 : ℝ))
  rw [show (11 / 15 : ℝ) = 2 * (11 / 30) by norm_num, Real.cos_two_mul]
  nlinarith

theorem eleven_fifteenths_lt_arccos_of_le {C : ℝ}
    (hC0 : -1 ≤ C) (hC1 : C ≤ 37 / 50) :
    11 / 15 < Real.arccos C := by
  rw [← Real.arccos_cos (x := 11 / 15) (by norm_num) (by linarith [Real.pi_gt_three])]
  exact Real.arccos_lt_arccos hC0
    (by linarith [cos_eleven_fifteenths_gt_thirty_seven_fiftieths]) (Real.cos_le_one _)

/-- In the pre-floor case, the exact zero-source circle gives both a
short excess height and an early first zero. -/
theorem initial_circle_excess_bounds {d B a : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d < 111 / 50)
    (hB0 : -7 / 12 < B) (hB1 : B < 7 / 40)
    (ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hp : initialFloorCircleP d B a = 0)
    (hq : 1 < initialFloorCircleQ d B a) :
    a < Real.pi / 6 ∧ initialFloorCircleQ d B a - 1 < 1 / 12 ∧
      quadraticExcessLength (initialFloorCircleQ d B a - 1) < 1 / 6 := by
  have hr := initialFloorCircle_radius d B a
  rw [hp] at hr
  have hB : B < 0 := by nlinarith
  have hqbound : initialFloorCircleQ d B a - 1 < 1 / 12 := by nlinarith
  refine ⟨?_, hqbound, quadraticExcessLength_lt (by linarith) (by norm_num) (by linarith)⟩
  by_contra! h
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ha.2.le h
  rw [Real.sin_pi_div_six] at this
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ha.1, Real.pi_pos], ha.2⟩
  unfold initialFloorCircleP at hp
  linarith [mul_neg_of_neg_of_pos hB hc, mul_nonneg (sub_nonneg.2 hd0)
    (Real.sin_nonneg_of_nonneg_of_le_pi ha.1.le (by linarith [ha.2, Real.pi_pos]))]


/-- The existing 3–4–5 circle direction gives the upper height endpoint
`1 - 4/5`; its chord excludes positive momentum throughout the rest. -/
theorem initial_floor_positive_forces_small_tilt {d B h : ℝ}
    (hd : 2 ≤ d) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hB : B ≤ -1 / 4 + 5 / 4 * h)
    (hpositive : 0 < 1 + B * (1 - h) - d * initialFloorSine h) : h < 1 / 5 := by
  by_contra! hlow
  have hs : (1 + h) / 2 ≤ initialFloorSine h :=
    Real.le_sqrt_of_sq_le (by
      nlinarith only [mul_nonneg (show 0 ≤ 1 - h by linarith only [hh1])
        (show 0 ≤ 5 * h - 1 by linarith only [hlow])])
  nlinarith [mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ 1 - h),
    mul_nonneg (sub_nonneg.2 hd) (initialFloorSine_nonneg h)]

private theorem floor_test_tilt_loss {d B h : ℝ}
    (hd : 2 ≤ d) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5)
    (hB0 : -7 / 12 ≤ B) (hB1 : B ≤ -1 / 4 + 5 / 4 * h) :
    initialFloorTest d B h ≤ d ^ 2 - 3 / 16 - 5 * h := by
  have hs : 3 * h ≤ initialFloorSine h := Real.le_sqrt_of_sq_le (by nlinarith)
  have hprod := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ d)
  have hm := initialFloorTest_mono_B (d := d) hB1
    (by linarith : 0 ≤ B + (-1 / 4 + 5 / 4 * h) + 1 - h)
  unfold initialFloorTest at hm ⊢
  nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh1),
    mul_nonneg (sub_nonneg.mpr hd) hh0]

private theorem crossing_delay_le_height {d h a : ℝ}
    (hd : 2 ≤ d) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5) (had : a ≤ d)
    (hquad : 0 ≤ 3 / 4 + 5 / 4 * h - d * a + a ^ 2 / 2) :
    a ≤ properFirstZeroTime d (3 / 4) + h := by
  have hX := Real.sq_sqrt (show 0 ≤ d ^ 2 - 2 * (3 / 4) by nlinarith)
  have hX0 : 3 / 2 ≤ properCrossingRoot d (3 / 4) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  unfold properCrossingRoot at hX0
  unfold properFirstZeroTime properCrossingRoot
  by_contra! ha
  have hsq : (Real.sqrt (d ^ 2 - 2 * (3 / 4)) - h) ^ 2 ≤ (d - a) ^ 2 := by
    nlinarith [mul_nonneg hh0 (by linarith :
      0 ≤ 2 * Real.sqrt (d ^ 2 - 2 * (3 / 4)) - h - 5 / 2)]
  have hp := mul_pos (by linarith : 0 < Real.sqrt (d ^ 2 - 2 * (3 / 4)) - h - (d - a))
    (by linarith : 0 < Real.sqrt (d ^ 2 - 2 * (3 / 4)) - h + (d - a))
  nlinarith only [hsq, hp]

/-- The tilt delay is paid by the loss of floor energy, uniformly in width and height. -/
theorem tilted_excess_stops_early {d B h ε a : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5)
    (hB0 : -7 / 12 ≤ B) (hB1 : B ≤ -1 / 4 + 5 / 4 * h)
    (hε : 0 ≤ ε) (had : a ≤ d)
    (henergy : (2 + ε) ^ 2 ≤ initialFloorTest d B h)
    (hquad : 0 ≤ 1 + B - d * a + a ^ 2 / 2) :
    ε < 19 / 100 ∧ quadraticExcessLength ε < 1 / 3 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  have htest := floor_test_tilt_loss hd0 hh0 hh1 hB0 hB1
  have hE : (2 + ε) ^ 2 + 5 * h ≤ d ^ 2 - 3 / 16 := by linarith
  have he : ε < 19 / 100 := by nlinarith only [hE, hε, hd0, hd1, hh0]
  have hl := quadraticExcessLength_lt hε (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by nlinarith only [hE, hε, hd0, hd1, hh0])
  refine ⟨he, hl, ?_⟩
  have ha := crossing_delay_le_height hd0 hh0 hh1 had (by linarith)
  have hYsq : properEnergyRoot d (3 / 4) 0 ^ 2 = d ^ 2 - 3 / 16 := by
    unfold properEnergyRoot
    convert Real.sq_sqrt (show 0 ≤ d ^ 2 - 3 / 16 by nlinarith) using 1
    norm_num
  have hY0 : 0 ≤ properEnergyRoot d (3 / 4) 0 := Real.sqrt_nonneg _
  have hY1 : properEnergyRoot d (3 / 4) 0 < 9 / 4 := by nlinarith only [hYsq, hY0, hd0, hd1]
  have hY : 2 + ε ≤ properEnergyRoot d (3 / 4) 0 := by
    nlinarith only [hYsq, hY0, hE, hε, hh0]
  have hYgain : h ≤ properEnergyRoot d (3 / 4) 0 - (2 + ε) := by
    nlinarith only [hYsq, hE, hY, hY1, hε, mul_nonneg (sub_nonneg.mpr hY) (by linarith :
      0 ≤ 5 - (properEnergyRoot d (3 / 4) 0 + (2 + ε)))]
  have hZsq : properDecayRoot d (3 / 4) 0 ^ 2 = 4 * properEnergyRoot d (3 / 4) 0 - 7 :=
    Real.sq_sqrt (by linarith)
  have hZ0 : 0 ≤ properDecayRoot d (3 / 4) 0 := Real.sqrt_nonneg _
  have hZ1 : properDecayRoot d (3 / 4) 0 < 3 / 2 := by nlinarith only [hZsq, hZ0, hY1]
  have hLsq : (quadraticExcessLength ε + 1) ^ 2 = 1 + 4 * ε := by
    unfold quadraticExcessLength
    simp only [sub_add_cancel]
    exact Real.sq_sqrt (by linarith)
  have hL0 := quadraticExcessLength_nonneg hε
  have hZ : quadraticExcessLength ε + 1 ≤ properDecayRoot d (3 / 4) 0 := by
    nlinarith only [hZsq, hZ0, hLsq, hL0, hY]
  have hLgain : quadraticExcessLength ε + h ≤ properDecayLength d (3 / 4) 0 := by
    unfold properDecayLength
    nlinarith only [hZsq, hLsq, hYgain, hZ, mul_nonneg (sub_nonneg.mpr hZ) (by linarith :
      0 ≤ 4 - (properDecayRoot d (3 / 4) 0 + (quadraticExcessLength ε + 1)))]
  have hstop := zero_tilt_excess_stops_early hd0 hd1 (by norm_num) (le_refl (3 / 4 : ℝ))
  unfold properExcessEnd at hstop
  linarith

end AmbidextrousSofa.Analysis
