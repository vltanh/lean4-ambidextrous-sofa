module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# A uniform stopping estimate for horizontal curvature excess

The box pressure bounds and circle identity put the initial momentum-zero
crossing before `2/5`; the energy bounds its subsequent excess episode by
`1/3`. Thus the excess ends before a wall can reach a middle endpoint.
The width threshold is the endpoint energy equality for height one half.
The general parabola moments are retained for kernel integration.
-/

noncomputable section

namespace AmbidextrousSofa

def horizontalLeakageA0 (h : ℝ) : ℝ := h ^ 2 / 4 + h ^ 3 / 6

/-- The stopping angle times the integrated quadratic envelope. -/
def tiltedLeakageMomentBound : ℝ := (11 / 15) * horizontalLeakageA0 (1 / 3)

def horizontalLeakageA1 (h : ℝ) : ℝ := h ^ 3 / 12 + h ^ 4 / 16

theorem horizontalLeakageA0_nonneg {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ horizontalLeakageA0 h := by unfold horizontalLeakageA0; positivity

theorem horizontalLeakageA0_mono {h k : ℝ} (hh : 0 ≤ h) (hhk : h ≤ k) :
    horizontalLeakageA0 h ≤ horizontalLeakageA0 k := by unfold horizontalLeakageA0; gcongr

theorem horizontal_excess_stopping_bounds {C e : ℝ} (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50)
    (he0 : 1 / 2 - (1 - Real.sqrt (1 - C ^ 2)) / 4 ≤ e)
    (he1 : e ≤ 1 / 2 + 3 * (1 - Real.sqrt (1 - C ^ 2)) / 4) :
    0 < e ∧ e ≤ 3 * C * (2 / 5) - (2 / 5) ^ 2 / 2 ∧
      9 * C ^ 2 - e * (1 - e) ≤ (2 + ((1 / 3) ^ 2 + 2 * (1 / 3)) / 4) ^ 2 := by
  have hc0 : 0 ≤ C := by linarith
  have hc1 : C ≤ 4 / 5 := by linarith
  have hr := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - C ^ 2)
  have hs := Real.sqrt_nonneg (1 - C ^ 2)
  have hs0 : 3 / 5 ≤ Real.sqrt (1 - C ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hs1 : Real.sqrt (1 - C ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg C])
  have hH : 1 - Real.sqrt (1 - C ^ 2) ≤ 5 * C ^ 2 / 8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr hs1)]
  have hH1 : 1 - Real.sqrt (1 - C ^ 2) ≤ 1 / 3 := by nlinarith
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hC0) (sub_nonneg.mpr hc1)]
  · have heabs : (e - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ e - 1 / 4 by linarith)
        (show 0 ≤ 3 / 4 - e by linarith)]
    nlinarith

/-- With dry middle endpoints, both axis heights are one half. The energy
criterion is therefore `9C² ≤ 4 + 1/4`. -/
def horizontalEnergyWidth : ℝ := Real.sqrt 17 / 6

theorem horizontalEnergyWidth_spec :
    0 ≤ horizontalEnergyWidth ∧ horizontalEnergyWidth < 1 ∧
      9 * horizontalEnergyWidth ^ 2 = 17 / 4 := by
  have hs := Real.sqrt_nonneg (17 : ℝ)
  have hsq : Real.sqrt (17 : ℝ) ^ 2 = 17 := by norm_num [Real.sq_sqrt]
  unfold horizontalEnergyWidth
  constructor
  · positivity
  constructor <;> nlinarith

theorem horizontalEnergyWidth_gt_two_thirds : (2 / 3 : ℝ) < horizontalEnergyWidth := by
  obtain ⟨h0, -, hsq⟩ := horizontalEnergyWidth_spec
  nlinarith

theorem horizontal_energy_of_intrinsic_width {C : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ horizontalEnergyWidth) : 9 * C ^ 2 ≤ 17 / 4 := by
  have hsq : C ^ 2 ≤ horizontalEnergyWidth ^ 2 := by gcongr
  linarith [horizontalEnergyWidth_spec.2.2]

end AmbidextrousSofa
