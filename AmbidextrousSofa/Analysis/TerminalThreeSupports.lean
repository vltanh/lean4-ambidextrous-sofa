module

public import AmbidextrousSofa.Analysis.TerminalWallBound
public import AmbidextrousSofa.Analysis.PartialTopInsertion

@[expose] public section

/-!
# Three actual supports at a proper terminal angle

The two diagonal supports and the first terminal support give simultaneous
upper bounds for the actual cap roof and lower bounds for its actual
partial barrier. The latter retains the whole outgoing first wall.

The terminal position is obtained from the support maximum of the cap.
Its compatibility with the diagonal position is proved at actual support
points. The top-endpoint alternatives likewise come from actual points of
a height-one affine-middle joint maximum. No realizability assumptions
are imposed on independent scalar parameters.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def terminalSlope (α : ℝ) : ℝ := Real.cos α / Real.sin α

def terminalSupportPosition (U : Set Plane) (α : ℝ) : ℝ :=
  (support U (unitNormal α) - Real.sin α) / Real.cos α

def terminalInset (α : ℝ) : ℝ := (1 - Real.sin α) / Real.cos α

theorem terminalSlope_pos {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    0 < terminalSlope α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  exact div_pos hc hs

theorem terminal_cos_le_sin {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α < Real.pi / 2) : Real.cos α ≤ Real.sin α := by
  have hαmem : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo hαmem
  have ht : 1 ≤ Real.tan α := by
    have h := Real.strictMonoOn_tan.monotoneOn
      (show Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      hαmem hα0
    simpa only [Real.tan_pi_div_four] using h
  rw [Real.tan_eq_sin_div_cos] at ht
  simpa only [one_mul] using (le_div_iff₀ hc).mp ht

theorem terminalSlope_le_one {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α < Real.pi / 2) : terminalSlope α ≤ 1 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  apply (div_le_iff₀ hs).mpr
  simpa only [one_mul] using terminal_cos_le_sin hα0 hαL

theorem terminalInset_pos {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    0 < terminalInset α := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hs : Real.sin α < 1 := by
    nlinarith [Real.sin_le_one α, Real.sin_sq_add_cos_sq α, sq_pos_of_pos hc]
  exact div_pos (sub_pos.mpr hs) hc

theorem terminal_sqrt_one_add_slope_sq {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    Real.sqrt (1 + terminalSlope α ^ 2) = 1 / Real.sin α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  unfold terminalSlope
  field_simp [hs.ne'] <;> nlinarith [Real.sin_sq_add_cos_sq α]

theorem terminalSlope_mul_inset {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalSlope α * terminalInset α =
      Real.sqrt (1 + terminalSlope α ^ 2) - 1 := by
  have hs : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos α ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩).ne'
  rw [terminal_sqrt_one_add_slope_sq hα0 hαL]
  unfold terminalSlope terminalInset
  field_simp [hs, hc] <;> ring

theorem terminalInset_eq_slope_div_one_add_sqrt {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α = terminalSlope α /
      (1 + Real.sqrt (1 + terminalSlope α ^ 2)) := by
  have hs : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos α ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩).ne'
  have hden : 1 + Real.sqrt (1 + terminalSlope α ^ 2) ≠ 0 := by positivity
  apply (eq_div_iff hden).mpr
  rw [terminal_sqrt_one_add_slope_sq hα0 hαL]
  unfold terminalSlope terminalInset
  field_simp [hs, hc] <;> nlinarith [Real.sin_sq_add_cos_sq α]

theorem terminal_support_line_eq (U : Set Plane) {α : ℝ}
    (hs : Real.sin α ≠ 0) (hc : Real.cos α ≠ 0) (x : ℝ) :
    support U (unitNormal α) / Real.sin α - terminalSlope α * x =
      1 - terminalSlope α * (x - terminalSupportPosition U α) := by
  unfold terminalSlope terminalSupportPosition
  field_simp [hs, hc] <;> ring

theorem firstWall_eq_terminal_parameters (U : Set Plane) {α : ℝ}
    (hs : Real.sin α ≠ 0) (hc : Real.cos α ≠ 0) (x : ℝ) :
    firstWall U α x = terminalSlope α *
      (terminalSupportPosition U α - terminalInset α - x) := by
  unfold firstWall terminalSlope terminalSupportPosition terminalInset
  field_simp [hs, hc] <;> ring

theorem IsDownwardCap.capRoof_le_terminal_support {U : Set Plane}
    (hU : IsDownwardCap U) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 - terminalSlope α * (x - terminalSupportPosition U α) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have h := hU.capRoof_le_first_support_line hs hx
  change capRoof U x ≤ support U (unitNormal α) / Real.sin α - terminalSlope α * x at h
  rwa [terminal_support_line_eq U hs.ne' hc.ne' x] at h

/-- The visited diagonal corner and the entire terminal first wall are
both actual lower bounds for the partial barrier. -/
theorem IsDownwardCap.three_supports_le_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α < Real.pi / 2) (x : ℝ) :
    max (max 0 (min ((diagonalRight U - 1) - (Real.sqrt 2 - 1) - x)
      ((diagonalLeft U - 1) - (Real.sqrt 2 - 1) + x)))
      (terminalSlope α * (terminalSupportPosition U α - terminalInset α - x)) ≤
        partialBarrier U α x := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  refine max_le (max_le (partialBarrier_nonneg U α x) ?_) ?_
  · have h := cornerWall_pi_div_four_le_partialBarrier hU.isCompact hα0 hαL.le x
    rw [cornerWall, firstWall_pi_div_four_eq_diagonal hU,
      secondWall_pi_div_four_eq_diagonal hU] at h
    rw [show (diagonalRight U - 1) - (Real.sqrt 2 - 1) - x =
        diagonalRight U - Real.sqrt 2 - x by ring,
      show (diagonalLeft U - 1) - (Real.sqrt 2 - 1) + x =
        diagonalLeft U - Real.sqrt 2 + x by ring]
    exact h
  · rw [← firstWall_eq_terminal_parameters U hs.ne' hc.ne' x]
    exact le_max_right _ _

/-- The two first-support positions are compatible because they are
maxima on the same cap in the unit strip. -/
theorem IsDownwardCap.terminalSupportPosition_le_diagonal {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α < Real.pi / 2) :
    terminalSupportPosition U α ≤ diagonalRight U - 1 := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hsc := terminal_cos_le_sin hα0 hαL
  obtain ⟨p, hp, hpmax⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (unitNormal α)
  change p.1 * Real.cos α + p.2 * Real.sin α = support U (unitNormal α) at hpmax
  have hdiag := hU.diagonalRight_ge hp
  have hy := (hU.inStrip hp).2
  have hnegative := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy)
    (sub_nonneg.mpr hsc)
  unfold terminalSupportPosition
  apply (div_le_iff₀ hc).mpr
  nlinarith [mul_le_mul_of_nonneg_right hdiag hc.le]

theorem IsDownwardCap.diagonal_le_terminalSupportPosition {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α < Real.pi / 2) :
    diagonalRight U - 1 ≤ (1 - terminalSlope α) * horizontalRight U +
      terminalSlope α * terminalSupportPosition U α := by
  obtain ⟨p, hp, hpmax⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (1, 1)
  change p.1 * 1 + p.2 * 1 = diagonalRight U at hpmax
  simp only [mul_one] at hpmax
  have hx : p.1 ≤ horizontalRight U :=
    le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove ⟨p, hp, rfl⟩
  have hy := le_capRoof hU.isCompact hp
  have hroof := hU.capRoof_le_terminal_support
    (by linarith [Real.pi_pos] : 0 < α) hαL (show p.1 ∈ horizontalProjection U from ⟨p, hp, rfl⟩)
  have hmul := mul_nonneg (sub_nonneg.mpr (terminalSlope_le_one hα0 hαL))
    (sub_nonneg.mpr hx)
  nlinarith

theorem IsDownwardCap.terminalSupportPosition_le_right {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalSupportPosition U α ≤ horizontalRight U := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hsupp : support U (unitNormal α) ≤
      horizontalRight U * Real.cos α + Real.sin α := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    have hx : p.1 ≤ horizontalRight U :=
      le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove ⟨p, hp, rfl⟩
    have hy := (hU.inStrip hp).2
    change p.1 * Real.cos α + p.2 * Real.sin α ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hx hc.le,
      mul_le_mul_of_nonneg_right hy hs.le]
  unfold terminalSupportPosition
  apply (div_le_iff₀ hc).mpr
  linarith

theorem IsDownwardCap.three_support_compatibility_centered {U : Set Plane}
    (hU : IsDownwardCap U) {C α : ℝ}
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2) :
    terminalSupportPosition U α ≤ diagonalRight U - 1 ∧
    diagonalRight U - 1 ≤ 2 * (1 - terminalSlope α) * C +
      terminalSlope α * terminalSupportPosition U α ∧
    diagonalRight U - 1 ≤ 2 * C ∧ diagonalLeft U - 1 ≤ 2 * C ∧
    terminalSupportPosition U α ≤ 2 * C := by
  refine ⟨hU.terminalSupportPosition_le_diagonal hα0 hαL, ?_, ?_, ?_, ?_⟩
  · have h := hU.diagonal_le_terminalSupportPosition hα0 hαL
    rw [hright] at h
    nlinarith
  · have h := hU.diagonalRight_le
    rw [hright] at h
    linarith
  · have h := hU.diagonalLeft_le
    rw [hleft] at h
    linarith
  · simpa only [hright] using hU.terminalSupportPosition_le_right
      (by linarith [Real.pi_pos] : 0 < α) hαL

theorem IsDownwardCap.three_support_lower_of_top {U : Set Plane}
    (hU : IsDownwardCap U) {α t : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (ht : (t, 1) ∈ U) :
    -t ≤ diagonalLeft U - 1 ∧ t ≤ diagonalRight U - 1 ∧
      t ≤ terminalSupportPosition U α := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  refine ⟨by linarith [hU.diagonalLeft_ge ht], by linarith [hU.diagonalRight_ge ht], ?_⟩
  have hsupp := coordDot_le_support hU.isCompact ht (unitNormal α)
  change t * Real.cos α + 1 * Real.sin α ≤ _ at hsupp
  unfold terminalSupportPosition
  apply (le_div_iff₀ hc).mpr
  linarith

/-- The endpoint alternatives are actual points of the cap. Both slope
signs use their own top insertion, without reflecting the partial score. -/
theorem IsJointCapMaximizer.top_endpoint_of_affine {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hheight : capHeight U = 1) {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (horizontalLeft U + capWidth U / 4, 1) ∈ U ∨
      (horizontalRight U - capWidth U / 4, 1) ∈ U := by
  have hw : 0 ≤ capWidth U := hU.isCap.capWidth_nonneg
  by_cases hm : 0 ≤ m
  · right
    have hx : horizontalRight U - capWidth U / 4 ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      unfold capWidth at *
      constructor <;> linarith
    have hp := capRoof_mem hU.isCap.isCompact hx
    rwa [hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine] at hp
  · left
    have hx : horizontalLeft U + capWidth U / 4 ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      unfold capWidth at *
      constructor <;> linarith
    have hp := capRoof_mem hU.isCap.isCompact hx
    rwa [hU.middle_left_eq_one_of_affine_nonpos hheight (le_of_not_ge hm) haffine] at hp

theorem IsDownwardCap.capRoof_le_left_support_reward {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 - max (-x - (diagonalLeft U - 1)) 0 := by
  have hroof := hU.capRoof_le_diagonalLeft hx
  have hheight := capRoof_le_one hU.isCompact hU.inStrip x
  have hmax : max (-x - (diagonalLeft U - 1)) 0 ≤ 1 - capRoof U x :=
    max_le (by linarith) (by linarith)
  linarith

theorem IsDownwardCap.capRoof_le_right_support_reward {U : Set Plane}
    (hU : IsDownwardCap U) {α x : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 - max (max 0 (x - (diagonalRight U - 1)))
      (terminalSlope α * (x - terminalSupportPosition U α)) := by
  have hdiagonal := hU.capRoof_le_diagonalRight hx
  have hterminal := hU.capRoof_le_terminal_support hα0 hαL hx
  have hheight := capRoof_le_one hU.isCompact hU.inStrip x
  have hmax : max (max 0 (x - (diagonalRight U - 1)))
      (terminalSlope α * (x - terminalSupportPosition U α)) ≤ 1 - capRoof U x :=
    max_le (max_le (by linarith) (by linarith)) (by linarith)
  linarith

/-- Integrating the genuine three-support bounds gives the finite scalar
relaxation. The left reward uses only a change of integration variable;
the actual cap and its partial barrier are never reflected. -/
theorem IsDownwardCap.capScore_le_three_support_integrals_centered
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ 2 * C -
      (∫ x in C..(2 * C), max (x - (diagonalLeft U - 1)) 0) -
      (∫ x in C..(2 * C), max (max 0 (x - (diagonalRight U - 1)))
        (terminalSlope α * (x - terminalSupportPosition U α))) -
      ∫ x in (-C)..C,
        max (max 0 (min ((diagonalRight U - 1) - (Real.sqrt 2 - 1) - x)
          ((diagonalLeft U - 1) - (Real.sqrt 2 - 1) + x)))
          (terminalSlope α * (terminalSupportPosition U α - terminalInset α - x)) := by
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1
  let k := terminalSlope α
  let b := terminalSupportPosition U α
  let d := terminalInset α
  let K := Real.sqrt 2 - 1
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  have hprojection : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
  have hleftLoss : Continuous (fun x : ℝ => max (-x - v) 0) := by fun_prop
  have hrightLoss : Continuous (fun x : ℝ => max (max 0 (x - u)) (k * (x - b))) := by
    fun_prop
  have hniche : Continuous (fun x : ℝ => max (max 0 (min (u - K - x) (v - K + x)))
      (k * (b - d - x))) := by fun_prop
  have hleftReward : (∫ x in (-2 * C)..(-C), capRoof U x) ≤
      C - ∫ x in C..(2 * C), max (x - v) 0 := by
    have hmono := intervalIntegral.integral_mono_on (by linarith : -2 * C ≤ -C)
      (hU.intervalIntegrable_capRoof (-2 * C) (-C))
      ((continuous_const.sub hleftLoss).intervalIntegrable (-2 * C) (-C))
      (fun x hx => hU.capRoof_le_left_support_reward (by
        rw [hprojection]
        exact ⟨hx.1, by linarith [hx.2]⟩))
    have hreflect : (∫ x in (-2 * C)..(-C), max (-x - v) 0) =
        ∫ x in C..(2 * C), max (x - v) 0 := by
      have h := intervalIntegral.integral_comp_neg (f := fun x : ℝ => max (x - v) 0)
        (a := -2 * C) (b := -C)
      rw [show -(-C) = C by ring, show -(-2 * C) = 2 * C by ring] at h
      exact h
    simp only [Pi.sub_apply] at hmono
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hleftLoss.intervalIntegrable _ _), intervalIntegral.integral_const,
      hreflect] at hmono
    simpa only [smul_eq_mul, mul_one, show -C - -2 * C = C by ring] using hmono
  have hrightReward : (∫ x in C..(2 * C), capRoof U x) ≤
      C - ∫ x in C..(2 * C), max (max 0 (x - u)) (k * (x - b)) := by
    have hmono := intervalIntegral.integral_mono_on (by linarith : C ≤ 2 * C)
      (hU.intervalIntegrable_capRoof C (2 * C))
      ((continuous_const.sub hrightLoss).intervalIntegrable C (2 * C))
      (fun x hx => hU.capRoof_le_right_support_reward hαpos hαL (by
        rw [hprojection]
        exact ⟨by linarith [hx.1], hx.2⟩))
    simp only [Pi.sub_apply] at hmono
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hrightLoss.intervalIntegrable _ _), intervalIntegral.integral_const] at hmono
    simpa only [smul_eq_mul, mul_one, show 2 * C - C = C by ring] using hmono
  have hmiddleCost : (∫ x in (-C)..C,
      max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x))) ≤
        ∫ x in (-C)..C, partialBarrier U α x := by
    exact intervalIntegral.integral_mono_on (by linarith : -C ≤ C)
      (hniche.intervalIntegrable (-C) C)
      (hU.intervalIntegrable_partialBarrier hαpos hαL.le (-C) C)
      (fun x _ => hU.three_supports_le_partialBarrier hα0 hαL x)
  have hscore := capScore_centered_quarters hU hleft hright α
  change capScore U α ≤ 2 * C - (∫ x in C..(2 * C), max (x - v) 0) -
    (∫ x in C..(2 * C), max (max 0 (x - u)) (k * (x - b))) -
      ∫ x in (-C)..C, max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x))
  linarith

end AmbidextrousSofa
