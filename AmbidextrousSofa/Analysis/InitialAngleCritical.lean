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

theorem initialAngle_integral_affine (m c a b : ℝ) :
    (∫ x in a..b, m * x + c) = m * (b ^ 2 - a ^ 2) / 2 + c * (b - a) := by
  have hc : Continuous (fun x : ℝ => m * x) := by fun_prop
  rw [intervalIntegral.integral_add (hc.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

end AmbidextrousSofa
