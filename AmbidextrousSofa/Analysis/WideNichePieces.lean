module

public import AmbidextrousSofa.Analysis.WideSupportCuts

@[expose] public section

/-!
# Actual additional niche pieces before their baseline zeros

Each piece is integrated only from its diagonal crossover to the earlier
of its two-wall peak and its diagonal baseline zero. The nonpositive
piece case contributes zero. This is an ordinary spatial integral and
does not assume that the untruncated piece fits inside the baseline.
The intercepts of the two nearby support lines are recorded here.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def wideCrossing (k u b : ℝ) : ℝ := (u - k - b) / (1 + k)
def widePeak (k b B : ℝ) : ℝ := (B - b) / (2 * (1 + k))
def wideGain (k u b B : ℝ) : ℝ := (B + b) / 2 - u + k
def wideBaselineGain (k u b : ℝ) : ℝ := (1 + k) * (u - k - wideCrossing k u b)
def wideTruncatedGain (k u b B : ℝ) : ℝ := min (wideGain k u b B) (wideBaselineGain k u b)

theorem wideTruncatedGain_eq_sub_loss (k u b B : ℝ) :
    wideTruncatedGain k u b B =
      wideGain k u b B - max (wideGain k u b B - wideBaselineGain k u b) 0 :=
  min_eq_left_sub_positive _ _

theorem wide_rising_piece_integral {n : ℝ → ℝ} {A k u v b B : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hn : ∀ l r, IntervalIntegrable n volume l r)
    (hfloor : ∀ x, max (min (u - k - x) (v - k + x)) 0 ≤ n x)
    (hwall : ∀ x, min (b + k * x) (B - x / k) ≤ n x)
    (hd : (u - v) / 2 ≤ A)
    (hc : (u - v) / 2 ≤ wideCrossing k u b)
    (hp : widePeak k b B ≤ A) :
    (max (wideTruncatedGain k u b B) 0) ^ 2 / (2 * (1 + k)) ≤
      ∫ x in ((u - v) / 2)..A, n x - max (min (u - k - x) (v - k + x)) 0 := by
  set l := wideCrossing k u b
  have hkR : 0 < 1 + k := add_pos one_pos hk
  have hl : (1 + k) * l = u - k - b := mul_div_cancel₀ _ hkR.ne'
  have hp2 : widePeak k b B * (2 * (1 + k)) = B - b := div_mul_cancel₀ _ (by positivity)
  have hf : ∀ a z, IntervalIntegrable (fun x => n x - max (min (u - k - x) (v - k + x)) 0)
      volume a z := fun a z => (hn a z).sub (Continuous.intervalIntegrable (by fun_prop) a z)
  have hf0 (x : ℝ) : 0 ≤ n x - max (min (u - k - x) (v - k + x)) 0 := sub_nonneg.mpr (hfloor x)
  have hH : wideTruncatedGain k u b B = (1 + k) * (min (widePeak k b B) (u - k) - l) := by
    rw [← min_sub_sub_right, mul_min_of_nonneg _ _ hkR.le, wideTruncatedGain, wideGain]
    congr 1
    linarith only [hl, hp2]
  rcases le_or_gt (wideTruncatedGain k u b B) 0 with hpos | hpos
  · rw [max_eq_right hpos, zero_pow two_ne_zero, zero_div]
    exact intervalIntegral.integral_nonneg_of_forall hd hf0
  set r := min (widePeak k b B) (u - k)
  have hlr : l ≤ r := (sub_pos.mp (pos_of_mul_pos_right (hH ▸ hpos) hkR.le)).le
  have hcut : ∀ x ∈ Icc l r, (1 + k) * (x - l) ≤ n x - max (min (u - k - x) (v - k + x)) 0 := by
    rintro x ⟨-, hx⟩
    have hnear : b + k * x ≤ B - x / k := by
      rw [div_diagonal_offset hk hksq]
      linarith only [mul_le_mul_of_nonneg_left (hx.trans (min_le_left _ _)) hkR.le, hp2]
    have h1 := min_eq_left hnear ▸ hwall x
    have h2 := max_le (min_le_left (u - k - x) (v - k + x))
      (sub_nonneg.mpr (hx.trans (min_le_right _ _)))
    linarith only [h1, h2, hl]
  rw [max_eq_left hpos.le, hH]
  calc ((1 + k) * (r - l)) ^ 2 / (2 * (1 + k)) = ∫ x in l..r, (1 + k) * (x - l) := by
        simp; field_simp; ring
    _ ≤ _ := intervalIntegral.integral_mono_on hlr (Continuous.intervalIntegrable (by fun_prop) _ _)
        (hf l r) hcut
    _ ≤ _ := intervalIntegral.integral_mono_interval hc hlr ((min_le_left _ _).trans hp)
        (Eventually.of_forall hf0) (hf _ _)

def wideNearRightIntercept (U : Set Plane) (k : ℝ) : ℝ := support U (-k, 1) - nearDiagonalNorm k
def wideNearLeftIntercept (U : Set Plane) (k : ℝ) : ℝ := support U (k, 1) - nearDiagonalNorm k
def wideEndpointIntercept (a e k : ℝ) : ℝ := e + (a - nearDiagonalNorm k) / k

end AmbidextrousSofa
