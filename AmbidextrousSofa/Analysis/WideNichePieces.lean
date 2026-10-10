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

theorem wideGain_eq_peak_difference {k : ℝ} (hk : 0 < k) (u b B : ℝ) :
    wideGain k u b B = (1 + k) * (widePeak k b B - wideCrossing k u b) := by
  unfold wideGain widePeak wideCrossing
  field_simp [(by linarith only [hk] : 1 + k ≠ 0)] <;> ring

theorem wideTruncatedGain_eq {k : ℝ} (hk : 0 < k) (u b B : ℝ) :
    wideTruncatedGain k u b B =
      (1 + k) * (min (widePeak k b B) (u - k) - wideCrossing k u b) := by
  unfold wideTruncatedGain wideBaselineGain
  rw [wideGain_eq_peak_difference hk, ← min_sub_sub_right,
    mul_min_of_nonneg _ _ (by linarith only [hk] : 0 ≤ 1 + k)]

theorem wideTruncatedGain_eq_sub_loss (k u b B : ℝ) :
    wideTruncatedGain k u b B =
      wideGain k u b B - max (wideGain k u b B - wideBaselineGain k u b) 0 := by
  exact min_eq_left_sub_positive _ _

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
  let f : ℝ → ℝ := fun x => n x - max (min (u - k - x) (v - k + x)) 0
  let l := wideCrossing k u b
  let r := min (widePeak k b B) (u - k)
  let H := wideTruncatedGain k u b B
  have hkR : 0 < 1 + k := by linarith only [hk]
  have hf : ∀ a z, IntervalIntegrable f volume a z := fun a z =>
    (hn a z).sub ((show Continuous (fun x : ℝ => max (min (u - k - x) (v - k + x)) 0)
      by fun_prop).intervalIntegrable a z)
  have hf0 (x : ℝ) : 0 ≤ f x := sub_nonneg.mpr (hfloor x)
  have hH : H = (1 + k) * (r - l) := wideTruncatedGain_eq hk u b B
  change (max H 0) ^ 2 / (2 * (1 + k)) ≤ ∫ x in ((u - v) / 2)..A, f x
  by_cases hpos : 0 < H
  · have hlr : l ≤ r := by
      have h := (mul_pos_iff_of_pos_left hkR).mp (hH ▸ hpos)
      linarith only [h]
    have hrA : r ≤ A := (min_le_left _ _).trans hp
    have hlEq : (1 + k) * l = u - k - b := mul_div_cancel₀ _ hkR.ne'
    have hpEq : 2 * (1 + k) * widePeak k b B = B - b :=
      mul_div_cancel₀ _ (by positivity : 2 * (1 + k) ≠ 0)
    have hkInv : k + 1 / k = 2 * (1 + k) := by
      field_simp [hk.ne']
      nlinarith only [hksq]
    have hcut : ∀ x ∈ Icc l r, (1 + k) * (x - l) ≤ f x := by
      intro x hx
      have hxd : (u - v) / 2 ≤ x := hc.trans hx.1
      have hxu : x ≤ u - k := hx.2.trans (min_le_right _ _)
      have hxp : x ≤ widePeak k b B := hx.2.trans (min_le_left _ _)
      have hnear : b + k * x ≤ B - x / k := by
        have hprod := mul_nonneg hkR.le (sub_nonneg.mpr hxp)
        have hki : (k + 1 / k) * x = 2 * (1 + k) * x := congrArg (fun z : ℝ => z * x) hkInv
        nlinarith only [hprod, hpEq, hki]
      have hwallx := hwall x
      rw [min_eq_left hnear] at hwallx
      have hdiag : max (min (u - k - x) (v - k + x)) 0 = u - k - x := by
        rw [min_eq_left (by linarith only [hxd]), max_eq_left (by linarith only [hxu])]
      dsimp [f]
      rw [hdiag]
      nlinarith only [hwallx, hlEq]
    have hlocal := intervalIntegral.integral_mono_on hlr
      ((show Continuous (fun x : ℝ => (1 + k) * (x - l)) by fun_prop).intervalIntegrable _ _)
      (hf l r) hcut
    have harea : (∫ x in l..r, (1 + k) * (x - l)) = H ^ 2 / (2 * (1 + k)) := by
      have h := integral_affine_scalar l r l (1 + k) 0
      simp only [zero_add, zero_mul] at h
      rw [h, hH]
      field_simp [hkR.ne'] <;> ring
    rw [harea] at hlocal
    rw [max_eq_left hpos.le]
    exact hlocal.trans (intervalIntegral.integral_mono_interval hc hlr hrA
      (Eventually.of_forall hf0) (hf _ _))
  · rw [max_eq_right (le_of_not_gt hpos)]
    simpa only [zero_pow, zero_div] using
      intervalIntegral.integral_nonneg_of_forall hd hf0

def wideNearRightIntercept (U : Set Plane) (k : ℝ) : ℝ := support U (-k, 1) - nearDiagonalNorm k
def wideNearLeftIntercept (U : Set Plane) (k : ℝ) : ℝ := support U (k, 1) - nearDiagonalNorm k
def wideEndpointIntercept (a e k : ℝ) : ℝ := e + (a - nearDiagonalNorm k) / k

theorem IsDownwardCap.wide_near_right_wall_le {U : Set Plane}
    (hU : IsDownwardCap U) {a k α : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    (hr : horizontalRight U = a)
    (hα : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    min (wideNearRightIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U a) k - x / k) ≤ partialBarrier U α x := by
  have hx : a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hr]
    exact ⟨by rw [← hr]; exact horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact, le_rfl⟩
  have hs := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (1, k)
  simp only [coordDot, mul_one] at hs
  have hcomp : wideEndpointIntercept a (capRoof U a) k - x / k ≤ firstWall U (Real.arctan k) x := by
    rw [hU.firstWall_arctan hk.ne']
    unfold wideEndpointIntercept
    apply (le_div_iff₀ hk).mpr
    have hmul : (capRoof U a + (a - nearDiagonalNorm k) / k - x / k) * k =
        a + capRoof U a * k - nearDiagonalNorm k - x := by field_simp [hk.ne'] <;> ring
    rw [hmul]
    linarith only [hs]
  have hsecond : wideNearRightIntercept U k + k * x = secondWall U (Real.arctan k) x := by
    rw [hU.secondWall_arctan]
    rfl
  have hwall := hU.cornerWall_le_partialBarrier_of_angle_le
    (Real.arctan_pos.mpr hk)
    ((arctan_le_complement_arctan hk1).trans hα) hαL x
  apply (min_le_min le_rfl hcomp).trans
  rw [hsecond, min_comm]
  exact hwall

theorem IsDownwardCap.wide_near_left_wall_le {U : Set Plane}
    (hU : IsDownwardCap U) {a k α : ℝ} (hk : 0 < k)
    (hl : horizontalLeft U = -a)
    (hα : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    min (wideNearLeftIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U (-a)) k - x / k) ≤ partialBarrier U α (-x) := by
  have hx : -a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl]
    exact ⟨le_rfl, by rw [← hl]; exact horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact⟩
  have hs := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (-1, k)
  simp only [coordDot, mul_neg_one, neg_neg] at hs
  have hcomp : wideEndpointIntercept a (capRoof U (-a)) k - x / k ≤
      secondWall U (Real.pi / 2 - Real.arctan k) (-x) := by
    rw [hU.secondWall_complement_arctan hk.ne']
    unfold wideEndpointIntercept
    apply (le_div_iff₀ hk).mpr
    have hmul : (capRoof U (-a) + (a - nearDiagonalNorm k) / k - x / k) * k =
        a + capRoof U (-a) * k - nearDiagonalNorm k - x := by field_simp [hk.ne'] <;> ring
    rw [hmul]
    linarith only [hs]
  have hfirst : wideNearLeftIntercept U k + k * x =
      firstWall U (Real.pi / 2 - Real.arctan k) (-x) := by
    rw [hU.firstWall_complement_arctan]
    unfold wideNearLeftIntercept
    ring
  have hwall := hU.cornerWall_le_partialBarrier_of_angle_le
    (sub_pos.mpr (Real.arctan_lt_pi_div_two k))
    hα hαL (-x)
  apply (min_le_min le_rfl hcomp).trans
  rw [hfirst]
  exact hwall

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
  have hα45 : Real.pi / 4 ≤ α := by
    have h := Real.arctan_strictMono.monotone hk1
    rw [Real.arctan_one] at h
    linarith only [h, hα]
  let n := partialBarrier U α
  let d := (u - v) / 2
  let f : ℝ → ℝ := fun x => n x - max (min (u - k - x) (v - k + x)) 0
  have hn : ∀ l r, IntervalIntegrable n volume l r :=
    hU.intervalIntegrable_partialBarrier hα0 hαL
  have hfloor (x : ℝ) : max (min (u - k - x) (v - k + x)) 0 ≤ n x := by
    simpa only [sub_zero, zero_add] using hU.tilted_diagonal_tent_le_partialBarrier
      (h := 0) hkoffset hu (by simpa only [sub_zero] using hv) hα45 hαL x
  have hright := wide_rising_piece_integral hk hksq hn hfloor
    (hU.wide_near_right_wall_le hk hk1 hr hα hαL) hd.2 hcR hpR
  have hnRef : ∀ l r, IntervalIntegrable (fun x => n (-x)) volume l r := by
    intro l r
    have h := (IntervalIntegrable.iff_comp_neg).mp (hn (-l) (-r))
    simpa only [neg_neg] using h
  have hfloorRef (x : ℝ) : max (min (v - k - x) (u - k + x)) 0 ≤ n (-x) := by
    have h := hfloor (-x)
    have hid : min (u - k - -x) (v - k + -x) = min (v - k - x) (u - k + x) := by
      rw [min_comm]
      congr 1 <;> ring
    rwa [hid] at h
  have hleft := wide_rising_piece_integral hk hksq hnRef hfloorRef
    (hU.wide_near_left_wall_le hk hl hα hαL)
    (show (v - u) / 2 ≤ a / 2 by linarith only [hd.1])
    (show (v - u) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k) by linarith only [hcL]) hpL
  have hleftInt :
      (∫ x in ((v - u) / 2)..(a / 2), n (-x) - max (min (v - k - x) (u - k + x)) 0) =
        ∫ x in (-a / 2)..d, f x := by
    have hfun (x : ℝ) : n (-x) - max (min (v - k - x) (u - k + x)) 0 = f (-x) := by
      dsimp [f]
      rw [min_comm]
      congr 3 <;> ring
    simp_rw [hfun]
    rw [intervalIntegral.integral_comp_neg]
    congr 1 <;> dsimp [d] <;> ring
  rw [hleftInt] at hleft
  change _ ≤ ∫ x in d..(a / 2), f x at hright
  have hf : ∀ l r, IntervalIntegrable f volume l r := fun l r =>
    (hn l r).sub ((show Continuous (fun x : ℝ => max (min (u - k - x) (v - k + x)) 0)
      by fun_prop).intervalIntegrable l r)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hf (-a / 2) d) (hf d (a / 2))
  have hdiag : (∫ x in (-a / 2)..(a / 2), max (min (u - k - x) (v - k + x)) 0) =
      (max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
        (max (v - k - a / 2) 0) ^ 2 / 2 := by
    simpa only [sub_zero] using integral_tilted_diagonal_tent k (h := 0)
      (show (u - v + 0) / 2 ∈ Icc (-a / 2) (a / 2) by simpa only [add_zero] using hd)
  have hwhole : (∫ x in (-a / 2)..(a / 2), f x) =
      (∫ x in (-a / 2)..(a / 2), n x) -
      ((max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
        (max (v - k - a / 2) 0) ^ 2 / 2) := by
    dsimp only [f]
    rw [intervalIntegral.integral_sub (hn _ _)
      ((show Continuous (fun x : ℝ => max (min (u - k - x) (v - k + x)) 0)
        by fun_prop).intervalIntegrable _ _), hdiag]
  rw [hwhole] at hadd
  have hgainSum :
      ((max (wideTruncatedGain k u (wideNearRightIntercept U k)
          (wideEndpointIntercept a (capRoof U a) k)) 0) ^ 2 +
       (max (wideTruncatedGain k v (wideNearLeftIntercept U k)
          (wideEndpointIntercept a (capRoof U (-a)) k)) 0) ^ 2) / (2 * (1 + k)) =
      (max (wideTruncatedGain k u (wideNearRightIntercept U k)
          (wideEndpointIntercept a (capRoof U a) k)) 0) ^ 2 / (2 * (1 + k)) +
      (max (wideTruncatedGain k v (wideNearLeftIntercept U k)
          (wideEndpointIntercept a (capRoof U (-a)) k)) 0) ^ 2 / (2 * (1 + k)) := add_div _ _ _
  rw [hgainSum]
  linarith only [hleft, hright, hadd]

end AmbidextrousSofa
