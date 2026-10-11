module

public import AmbidextrousSofa.Analysis.WideSupportCuts

@[expose] public section

/-!
# Actual additional niche pieces before their baseline zeros

Each piece is integrated only from its diagonal crossover to the earlier
of its two-wall peak and its diagonal baseline zero. The nonpositive
piece case contributes zero. This is an ordinary spatial integral and
does not assume that the untruncated piece fits inside the baseline.
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
    have hxk : x / k = x * (k + 2) := (div_eq_iff hk.ne').mpr (by linear_combination -x * hksq)
    have hnear : b + k * x ≤ B - x / k := by
      rw [hxk]
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

theorem IsDownwardCap.wide_near_right_wall_le {U : Set Plane}
    (hU : IsDownwardCap U) {a k α : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    (hr : horizontalRight U = a)
    (hα : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    min (wideNearRightIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U a) k - x / k) ≤ partialBarrier U α x := by
  have hs := coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (hr ▸ horizontalRight_mem hU.nonempty hU.isCompact)) (1, k)
  have hwall := hU.cornerWall_le_partialBarrier_of_angle_le (Real.arctan_pos.mpr hk)
    ((arctan_le_complement_arctan hk1).trans hα) hαL x
  rw [cornerWall, hU.firstWall_arctan hk.ne', hU.secondWall_arctan, min_comm] at hwall
  refine (min_le_min le_rfl ?_).trans hwall
  rw [wideEndpointIntercept, le_div_iff₀ hk, sub_mul, add_mul, div_mul_cancel₀ _ hk.ne',
    div_mul_cancel₀ _ hk.ne']
  simp only [coordDot] at hs
  linarith only [hs]

theorem IsDownwardCap.wide_near_left_wall_le {U : Set Plane}
    (hU : IsDownwardCap U) {a k α : ℝ} (hk : 0 < k)
    (hl : horizontalLeft U = -a)
    (hα : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    min (wideNearLeftIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U (-a)) k - x / k) ≤ partialBarrier U α (-x) := by
  have hs := coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (hl ▸ horizontalLeft_mem hU.nonempty hU.isCompact)) (-1, k)
  have hwall := hU.cornerWall_le_partialBarrier_of_angle_le
    (sub_pos.mpr (Real.arctan_lt_pi_div_two k)) hα hαL (-x)
  rw [cornerWall, hU.firstWall_complement_arctan, hU.secondWall_complement_arctan hk.ne'] at hwall
  refine (min_le_min (le_of_eq (by rw [wideNearLeftIntercept]; ring)) ?_).trans hwall
  rw [wideEndpointIntercept, le_div_iff₀ hk, sub_mul, add_mul, div_mul_cancel₀ _ hk.ne',
    div_mul_cancel₀ _ hk.ne']
  simp only [coordDot] at hs
  linarith only [hs]

/-- The two additional literal pieces are disjoint at the diagonal
apex. Their whole retained areas add to the diagonal niche integral. -/
theorem IsDownwardCap.wide_niche_integral_ge_pieces {U : Set Plane}
    (hU : IsDownwardCap U) {a k u v α : ℝ}
    (hk : 0 < k) (hk1 : k ≤ 1) (hksq : k ^ 2 + 2 * k = 1)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 + v)
    (hα : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2)
    (hd : (u - v) / 2 ∈ Icc (-a / 2) (a / 2))
    (hcR : (u - v) / 2 ≤ wideCrossing k u (wideNearRightIntercept U k))
    (hcL : -(u - v) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k))
    (hpR : widePeak k (wideNearRightIntercept U k) (wideEndpointIntercept a (capRoof U a) k) ≤ a / 2)
    (hpL : widePeak k (wideNearLeftIntercept U k) (wideEndpointIntercept a (capRoof U (-a)) k) ≤ a / 2) :
    (max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
      (max (v - k - a / 2) 0) ^ 2 / 2 +
      ((max (wideTruncatedGain k u (wideNearRightIntercept U k)
          (wideEndpointIntercept a (capRoof U a) k)) 0) ^ 2 +
       (max (wideTruncatedGain k v (wideNearLeftIntercept U k)
          (wideEndpointIntercept a (capRoof U (-a)) k)) 0) ^ 2) / (2 * (1 + k)) ≤
      ∫ x in (-a / 2)..(a / 2), partialBarrier U α x := by
  have hα0 : 0 < α := (sub_pos.mpr (Real.arctan_lt_pi_div_two k)).trans_le hα
  set n := partialBarrier U α
  have hn : ∀ l r, IntervalIntegrable n volume l r := hU.intervalIntegrable_partialBarrier hα0 hαL
  have htent : Continuous fun x => max (min (u - k - x) (v - k + x)) 0 := by fun_prop
  have hfloor (x : ℝ) : max (min (u - k - x) (v - k + x)) 0 ≤ n x := by
    simpa only [sub_zero, zero_add] using hU.tilted_diagonal_tent_le_partialBarrier (h := 0)
      hkoffset hu (by rwa [sub_zero]) (by linarith only [arctan_le_complement_arctan hk1, hα]) hαL x
  have hright := wide_rising_piece_integral hk hksq hn hfloor
    (hU.wide_near_right_wall_le hk hk1 hr hα hαL) hd.2 hcR hpR
  have hleft := wide_rising_piece_integral (n := fun x => n (-x)) hk hksq
    (fun l r => by simpa only [neg_neg] using (IntervalIntegrable.iff_comp_neg).mp (hn (-l) (-r)))
    (fun x => by have h := hfloor (-x); rwa [sub_neg_eq_add, ← sub_eq_add_neg, min_comm] at h)
    (hU.wide_near_left_wall_le hk hl hα hαL) (by linarith only [hd.1]) (by linarith only [hcL]) hpL
  have hrefl := intervalIntegral.integral_comp_neg (a := (v - u) / 2) (b := a / 2)
    (fun x => n x - max (min (u - k - x) (v - k + x)) 0)
  simp only [← neg_div, neg_sub, sub_neg_eq_add, ← sub_eq_add_neg] at hrefl
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((hn (-a / 2) ((u - v) / 2)).sub (htent.intervalIntegrable _ _))
    ((hn ((u - v) / 2) (a / 2)).sub (htent.intervalIntegrable _ _))
  have hdiag := integral_tilted_diagonal_tent k (h := 0) (a := a) (u := u) (v := v)
    (by rwa [add_zero])
  simp only [sub_zero] at hdiag
  rw [intervalIntegral.integral_sub (hn (-a / 2) (a / 2)) (htent.intervalIntegrable _ _),
    hdiag] at hadd
  simp only [min_comm] at hleft
  rw [add_div _ _ (2 * (1 + k))]
  linarith only [hleft, hright, hadd, hrefl]

end AmbidextrousSofa
