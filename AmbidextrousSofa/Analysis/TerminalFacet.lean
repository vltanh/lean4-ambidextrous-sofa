module

public import AmbidextrousSofa.Analysis.ProperTailRegime

@[expose] public section

/-!
# Actual terminal facet coordinates and tail geometry

The terminal point is the actual upper endpoint of the first supporting
face. Its horizontal face width is the difference of the two actual
supporting endpoints. These definitions retain the full terminal atom.

In the proper tail regime the terminal point is the right middle endpoint
when the middle slope is negative, and the right endpoint of the top face
otherwise. Either way it lies at or to the right of the right middle
endpoint, with height strictly above the terminal sine. Consequently the
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
  rw [← MovingSofaOptimality.dot_uvec_pi_div_two, MovingSofaOptimality.dot_vminus_uvec,
    imported_supp_pi_div_two]

theorem IsDownwardCap.terminalTailPoint_mem {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : terminalTailPoint U α ∈ U :=
  (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody α).1

/-- The horizontal width is the terminal arclength atom times its sine. -/
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

/-- With a negative middle slope, the terminal tail point is the right middle endpoint. -/
theorem IsJointCapMaximizer.terminalTailPoint_eq_of_negative {U : Set Plane} {α m c : ℝ}
    (hU : IsJointCapMaximizer U α) (hregime : ProperTailRegime U α m) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalTailPoint U α =
      (horizontalRight U - capWidth U / 4, capRoof U (horizontalRight U - capWidth U / 4)) :=
  (hU.support_vertices_first_unused_gap haffine le_rfl (by simpa [affineNormalAngle] using hm.le)
    (hregime.negative hm).1 (by simp)).1.trans (hU.middle_support_vertices hm.ne haffine).2

/-- With a nonnegative middle slope, the terminal tail point is the right endpoint of the top
face. -/
theorem IsJointCapMaximizer.terminalTailPoint_eq_of_nonneg {U : Set Plane} {α m c : ℝ}
    (hU : IsJointCapMaximizer U α) (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (hm : 0 ≤ m) (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalTailPoint U α = ((MovingSofaOptimality.vminus U (Real.pi / 2)).1, 1) := by
  rw [terminalTailPoint, (hU.support_vertices_first_unused_gap haffine le_rfl le_rfl hαL
    fun h => by unfold affineNormalAngle at h; linarith [h.2, Real.arctan_nonneg.mpr hm]).1]
  exact Prod.ext rfl ((top_vminus_snd_eq_capHeight U).trans hheight)

/-- The terminal tail point lies at or to the right of the right middle endpoint, strictly above
height `sin α`. -/
theorem IsJointCapMaximizer.terminalTailPoint_bounds_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    horizontalRight U - capWidth U / 4 ≤ (terminalTailPoint U α).1 ∧
      Real.sin α < (terminalTailPoint U α).2 ∧ (terminalTailPoint U α).2 ≤ 1 := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [hU.terminalTailPoint_eq_of_negative hregime hm haffine]
    exact ⟨le_rfl, (hregime.negative hm).2, capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _⟩
  obtain ⟨_, hb, _⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith [hU.width_bounds.1, one_lt_M])
  have htop : (horizontalRight U - capWidth U / 4, capHeight U) ∈ U := by
    rw [hheight, ← hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine]
    exact capRoof_mem hU.isCap.isCompact hb
  rw [hU.terminalTailPoint_eq_of_nonneg hαL hheight hm haffine]
  exact ⟨(hU.isCap.fst_mem_top_face htop rfl).2,
    (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hU.angle_pos, Real.pi_pos]) le_rfl
      hαL).trans_eq Real.sin_pi_div_two, le_rfl⟩

theorem IsDownwardCap.terminalTailInset_bounds {U : Set Plane} (hU : IsDownwardCap U)
    {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hH : Real.sin α < (terminalTailPoint U α).2) :
    0 < terminalTailInset U α ∧ terminalTailInset U α < Real.cos α ∧
      0 < terminalTailReserve U α ∧
      terminalTailReserve U α ≤ Real.sin α * Real.cos α / (1 + Real.sin α) ∧
      terminalTailReserve U α < Real.cos α / 2 := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  have hs1 : Real.sin α < 1 := by nlinarith [Real.sin_sq_add_cos_sq α]
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
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  refine lt_max_of_lt_right ?_
  rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
  exact mul_pos (div_pos hc hs) (sub_pos.mpr hx)

end AmbidextrousSofa
