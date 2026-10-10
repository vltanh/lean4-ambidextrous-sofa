module

public import AmbidextrousSofa.Analysis.ProperTailRegime

@[expose] public section

/-!
# Actual terminal facet coordinates and tail geometry

The terminal point is the actual upper endpoint of the first supporting
face. Its horizontal face width is the difference of the two actual
supporting endpoints. These definitions retain the full terminal atom.

At a largest-angle canonical joint maximizer, the terminal point lies at
or to the right of the right middle endpoint, with height strictly above
the terminal sine. The negative case uses the proved same-cap completion
exclusion; the other cases use the actual top endpoint. Consequently the
outgoing wall has the exact positive inset and reserve bounds used by the
proper-terminal geometry.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def terminalTailPoint (U : Set Plane) (α : ℝ) : Plane := MovingSofaOptimality.vplus U α

def terminalFaceWidth (U : Set Plane) (α : ℝ) : ℝ :=
  (MovingSofaOptimality.vminus U α).1 - (MovingSofaOptimality.vplus U α).1

def terminalTailInset (U : Set Plane) (α : ℝ) : ℝ :=
  (1 - (terminalTailPoint U α).2 * Real.sin α) / Real.cos α

def terminalTailReserve (U : Set Plane) (α : ℝ) : ℝ :=
  Real.cos α - terminalTailInset U α

def terminalTailZero (U : Set Plane) (α : ℝ) : ℝ :=
  (terminalTailPoint U α).1 - terminalTailInset U α

theorem top_vminus_snd_eq_capHeight (U : Set Plane) :
    (MovingSofaOptimality.vminus U (Real.pi / 2)).2 = capHeight U := by
  have h : coordDot (MovingSofaOptimality.vminus U (Real.pi / 2)) (unitNormal (Real.pi / 2)) =
      angleSupport U (Real.pi / 2) := MovingSofaOptimality.dot_vminus_uvec U (Real.pi / 2)
  simpa only [coordDot, unitNormal, angleSupport, capHeight,
    Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add] using h

theorem IsDownwardCap.top_vminus_fst_ge_of_top {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : (x, capHeight U) ∈ U) :
    x ≤ (MovingSofaOptimality.vminus U (Real.pi / 2)).1 := by
  have htop : (x, capHeight U) ∈ MovingSofaOptimality.edge U (Real.pi / 2) := by
    refine ⟨hx, ?_⟩
    change coordDot (x, capHeight U) (unitNormal (Real.pi / 2)) = angleSupport U (Real.pi / 2)
    simp only [coordDot, unitNormal, angleSupport, capHeight,
      Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add]
  have h := MovingSofaOptimality.dot_vminus_le_dot hU.isCompact htop
  simp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi_div_two, Real.cos_pi_div_two,
    mul_neg, mul_one, mul_zero, add_zero] at h
  linarith

theorem IsDownwardCap.terminalTailPoint_mem {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : terminalTailPoint U α ∈ U :=
  (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody α).1

theorem IsDownwardCap.terminalFaceWidth_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : 0 ≤ Real.sin α) : 0 ≤ terminalFaceWidth U α :=
  sub_nonneg.mpr (hU.face_fst_order hs)

/-- The horizontal width is the terminal arclength atom times its sine.
No vanishing of this atom has been imposed. -/
theorem IsDownwardCap.terminalFaceWidth_eq_curvature_atom {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) :
    terminalFaceWidth U α = (upperCurvature U {α}).toReal * Real.sin α := by
  have h := congrArg Prod.fst (MovingSofaOptimality.proposition2_1_2 hU.imported_isConvexBody α).2
  change (MovingSofaOptimality.vplus U α).1 = (MovingSofaOptimality.vminus U α).1 +
    (upperCurvature U {α}).toReal * (-Real.sin α) at h
  unfold terminalFaceWidth
  nlinarith

theorem IsDownwardCap.terminalFaceWidth_eq_projection_measure {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : 0 ≤ Real.sin α) :
    terminalFaceWidth U α = volume.real (horizontalProjection (MovingSofaOptimality.edge U α)) := by
  rw [hU.horizontalProjection_edge hs, Real.volume_real_Icc_of_le (hU.face_fst_order hs)]
  rfl

theorem IsDownwardCap.terminal_vminus_eq {U : Set Plane} (hU : IsDownwardCap U)
    {α : ℝ} (hs : Real.sin α ≠ 0) :
    MovingSofaOptimality.vminus U α =
      ((terminalTailPoint U α).1 + terminalFaceWidth U α,
        (terminalTailPoint U α).2 - terminalFaceWidth U α * Real.cos α / Real.sin α) := by
  have hline : (MovingSofaOptimality.vminus U α).1 * Real.cos α +
      (MovingSofaOptimality.vminus U α).2 * Real.sin α =
      (MovingSofaOptimality.vplus U α).1 * Real.cos α + (MovingSofaOptimality.vplus U α).2 * Real.sin α :=
    (MovingSofaOptimality.dot_vminus_uvec U α).trans (MovingSofaOptimality.dot_vplus_uvec U α).symm
  apply Prod.ext
  · dsimp [terminalTailPoint, terminalFaceWidth]
    ring
  · dsimp [terminalTailPoint, terminalFaceWidth]
    field_simp [hs] <;> nlinarith only [hline]

/-- The three signs of the affine middle are handled on the original
orientation. No reflection of the outgoing wall is used. -/
theorem IsJointCapMaximizer.terminalTailPoint_bounds_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    horizontalRight U - capWidth U / 4 ≤ (terminalTailPoint U α).1 ∧
      Real.sin α < (terminalTailPoint U α).2 ∧ (terminalTailPoint U α).2 ≤ 1 := by
  by_cases hm : m < 0
  · obtain ⟨hαm, hH⟩ := hregime.negative hm
    have hmL : affineNormalAngle m < Real.pi / 2 := by
      have h := Real.arctan_lt_zero.mpr hm
      unfold affineNormalAngle
      linarith
    have hv := (hU.support_vertices_first_unused_gap haffine le_rfl hmL.le hαm
      (show affineNormalAngle m ∉ Ioo α (affineNormalAngle m) by simp)).1.trans
      (hU.middle_support_vertices hm.ne haffine).2
    change horizontalRight U - capWidth U / 4 ≤ (MovingSofaOptimality.vplus U α).1 ∧
      Real.sin α < (MovingSofaOptimality.vplus U α).2 ∧ (MovingSofaOptimality.vplus U α).2 ≤ 1
    rw [hv]
    exact ⟨le_rfl, hH, capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _⟩
  · have hm0 : 0 ≤ m := le_of_not_gt hm
    have hv := hU.first_terminal_vplus_of_middle_nonneg hαL hm0 haffine
    have hpy : (MovingSofaOptimality.vminus U (Real.pi / 2)).2 = 1 :=
      (top_vminus_snd_eq_capHeight U).trans hheight
    have hroof := hU.middle_right_eq_one_of_affine_nonneg hheight hm0 haffine
    obtain ⟨_, hb, _⟩ := hU.isCap.middleChord_endpoints
      (show 0 < capWidth U by linarith [hU.width_bounds.1, one_lt_M])
    have htop : (horizontalRight U - capWidth U / 4, capHeight U) ∈ U := by
      rw [hheight, ← hroof]
      exact capRoof_mem hU.isCap.isCompact hb
    have hx := hU.isCap.top_vminus_fst_ge_of_top htop
    have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hU.angle_pos, Real.pi_pos], hαL⟩
    have hs1 : Real.sin α < 1 := by
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_le_one α, sq_pos_of_pos hc]
    change horizontalRight U - capWidth U / 4 ≤ (MovingSofaOptimality.vplus U α).1 ∧
      Real.sin α < (MovingSofaOptimality.vplus U α).2 ∧ (MovingSofaOptimality.vplus U α).2 ≤ 1
    rw [hv, hpy]
    exact ⟨hx, hs1, le_rfl⟩

/-- The original largest-angle interface is preserved for the value
reduction; its proof now supplies only the local tail regime. -/
theorem IsJointCapMaximizer.terminalTailPoint_bounds
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    horizontalRight U - capWidth U / 4 ≤ (terminalTailPoint U α).1 ∧
      Real.sin α < (terminalTailPoint U α).2 ∧ (terminalTailPoint U α).2 ≤ 1 :=
  hU.terminalTailPoint_bounds_of_tail_regime
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

theorem IsDownwardCap.terminalTailInset_bounds {U : Set Plane} (hU : IsDownwardCap U)
    {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hH : Real.sin α < (terminalTailPoint U α).2) :
    0 < terminalTailInset U α ∧ terminalTailInset U α < Real.cos α ∧
      0 < terminalTailReserve U α ∧
      terminalTailReserve U α ≤ Real.sin α * Real.cos α / (1 + Real.sin α) ∧
      terminalTailReserve U α < Real.cos α / 2 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hH1 : (terminalTailPoint U α).2 ≤ 1 :=
    (hU.inStrip (hU.terminalTailPoint_mem α)).2
  have hs1 : Real.sin α < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_le_one α, sq_pos_of_pos hc]
  have hnum : 0 < 1 - (terminalTailPoint U α).2 * Real.sin α := by
    nlinarith [mul_le_mul_of_nonneg_right hH1 hs.le]
  have hd0 : 0 < terminalTailInset U α := div_pos hnum hc
  have hdc : terminalTailInset U α < Real.cos α := by
    apply (div_lt_iff₀ hc).mpr
    nlinarith [Real.sin_sq_add_cos_sq α, mul_pos (sub_pos.mpr hH) hs]
  have hden : 0 < 1 + Real.sin α := by positivity
  have hmin : (1 - Real.sin α) / Real.cos α ≤ terminalTailInset U α := by
    apply div_le_div_of_nonneg_right _ hc.le
    nlinarith [mul_le_mul_of_nonneg_right hH1 hs.le]
  have hidentity : Real.cos α - (1 - Real.sin α) / Real.cos α =
      Real.sin α * Real.cos α / (1 + Real.sin α) := by
    field_simp [hc.ne', hden.ne'] <;> nlinarith only [Real.sin_sq_add_cos_sq α]
  have hwbound : terminalTailReserve U α ≤
      Real.sin α * Real.cos α / (1 + Real.sin α) := by
    rw [← hidentity]
    exact sub_le_sub_left hmin _
  have hstrict : Real.sin α * Real.cos α / (1 + Real.sin α) < Real.cos α / 2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hc (sub_pos.mpr hs1)]
  exact ⟨hd0, hdc, sub_pos.mpr hdc, hwbound, hwbound.trans_lt hstrict⟩

/-- The actual outgoing wall, with its zero computed from the actual
upper terminal-face endpoint and its actual height. -/
theorem firstWall_eq_terminalTail (U : Set Plane) {α : ℝ}
    (hs : Real.sin α ≠ 0) (hc : Real.cos α ≠ 0) (x : ℝ) :
    firstWall U α x = (Real.cos α / Real.sin α) * (terminalTailZero U α - x) := by
  have hsupport : angleSupport U α = (terminalTailPoint U α).1 * Real.cos α +
      (terminalTailPoint U α).2 * Real.sin α := (MovingSofaOptimality.dot_vplus_uvec U α).symm
  change (angleSupport U α - 1 - x * Real.cos α) / Real.sin α = _
  rw [hsupport]
  unfold terminalTailZero terminalTailInset
  field_simp [hs, hc] <;> ring

theorem partialBarrier_pos_of_lt_terminalTailZero (U : Set Plane) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hx : x < terminalTailZero U α) :
    0 < partialBarrier U α x := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have h : 0 < firstWall U α x := by
    rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
    exact mul_pos (div_pos hc hs) (sub_pos.mpr hx)
  exact h.trans_le (le_max_right _ _)

end AmbidextrousSofa
