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
  simpa [coordDot, unitNormal, angleSupport, capHeight] using h

theorem IsDownwardCap.terminalTailPoint_mem {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : terminalTailPoint U α ∈ U :=
  (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody α).1

/-- The horizontal width is the terminal arclength atom times its sine.
No vanishing of this atom has been imposed. -/
theorem IsDownwardCap.terminalFaceWidth_eq_curvature_atom {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) :
    terminalFaceWidth U α = (upperCurvature U {α}).toReal * Real.sin α := by
  have h := congrArg Prod.fst (MovingSofaOptimality.proposition2_1_2 hU.imported_isConvexBody α).2
  change (MovingSofaOptimality.vplus U α).1 = (MovingSofaOptimality.vminus U α).1 +
    (upperCurvature U {α}).toReal * (-Real.sin α) at h
  rw [terminalFaceWidth, h]
  ring

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
  have h := (MovingSofaOptimality.proposition2_1_2 hU.imported_isConvexBody α).2
  simp only [terminalTailPoint, terminalFaceWidth, h, MovingSofaOptimality.vvec]
  ext
  · simp
  · field_simp
    simp
    ring

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
  rw [terminalTailPoint]
  by_cases hm : m < 0
  · obtain ⟨hαm, hH⟩ := hregime.negative hm
    have hmL : affineNormalAngle m < Real.pi / 2 := by
      rw [affineNormalAngle]; linarith [Real.arctan_lt_zero.mpr hm]
    rw [(hU.support_vertices_first_unused_gap haffine le_rfl hmL.le hαm (by simp)).1.trans
      (hU.middle_support_vertices hm.ne haffine).2]
    exact ⟨le_rfl, hH, capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _⟩
  · have hm0 : 0 ≤ m := le_of_not_gt hm
    obtain ⟨_, hb, _⟩ := hU.isCap.middleChord_endpoints
      (show 0 < capWidth U by linarith [hU.width_bounds.1, one_lt_M])
    have htop : (horizontalRight U - capWidth U / 4, capHeight U) ∈ U := by
      rw [hheight, ← hU.middle_right_eq_one_of_affine_nonneg hheight hm0 haffine]
      exact capRoof_mem hU.isCap.isCompact hb
    -- the top point lies on the top face, so at or before its right endpoint
    have hx := MovingSofaOptimality.dot_vminus_le_dot hU.isCap.isCompact (t := Real.pi / 2) ⟨htop,
      show coordDot (_, capHeight U) (unitNormal (Real.pi / 2)) = angleSupport U (Real.pi / 2) by
        simp [coordDot, unitNormal, angleSupport, capHeight]⟩
    simp [MovingSofaOptimality.dot, MovingSofaOptimality.vvec] at hx
    rw [hU.first_terminal_vplus_of_middle_nonneg hαL hm0 haffine, top_vminus_snd_eq_capHeight,
      hheight]
    exact ⟨by linarith,
      (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hU.angle_pos, Real.pi_pos]) le_rfl
        hαL).trans_eq Real.sin_pi_div_two, le_rfl⟩

theorem IsDownwardCap.terminalTailInset_bounds {U : Set Plane} (hU : IsDownwardCap U)
    {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hH : Real.sin α < (terminalTailPoint U α).2) :
    0 < terminalTailInset U α ∧ terminalTailInset U α < Real.cos α ∧
      0 < terminalTailReserve U α ∧
      terminalTailReserve U α ≤ Real.sin α * Real.cos α / (1 + Real.sin α) ∧
      terminalTailReserve U α < Real.cos α / 2 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  have hs1 : Real.sin α < 1 := (Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [Real.pi_pos]) le_rfl hαL).trans_eq Real.sin_pi_div_two
  have hH1 := (hU.inStrip (hU.terminalTailPoint_mem α)).2
  have hdc : terminalTailInset U α < Real.cos α :=
    (div_lt_iff₀ hc).mpr (by nlinarith [Real.sin_sq_add_cos_sq α])
  have hR : terminalTailReserve U α ≤ Real.sin α * Real.cos α / (1 + Real.sin α) := by
    rw [terminalTailReserve, terminalTailInset]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq α, mul_nonneg (mul_nonneg hs.le
      (by linarith : (0 : ℝ) ≤ 1 + Real.sin α)) (sub_nonneg.mpr hH1)]
  refine ⟨div_pos (by nlinarith) hc, hdc, sub_pos.mpr hdc, hR, hR.trans_lt ?_⟩
  rw [div_lt_div_iff₀ (by positivity) two_pos]
  nlinarith

/-- The actual outgoing wall, with its zero computed from the actual
upper terminal-face endpoint and its actual height. -/
theorem firstWall_eq_terminalTail (U : Set Plane) {α : ℝ}
    (hs : Real.sin α ≠ 0) (hc : Real.cos α ≠ 0) (x : ℝ) :
    firstWall U α x = (Real.cos α / Real.sin α) * (terminalTailZero U α - x) := by
  have h : support U (unitNormal α) = (terminalTailPoint U α).1 * Real.cos α +
      (terminalTailPoint U α).2 * Real.sin α := (MovingSofaOptimality.dot_vplus_uvec U α).symm
  rw [firstWall, h, terminalTailZero, terminalTailInset]
  field_simp
  ring

theorem partialBarrier_pos_of_lt_terminalTailZero (U : Set Plane) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hx : x < terminalTailZero U α) :
    0 < partialBarrier U α x := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  refine lt_max_of_lt_right ?_
  rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
  exact mul_pos (div_pos hc hs) (sub_pos.mpr hx)

end AmbidextrousSofa
