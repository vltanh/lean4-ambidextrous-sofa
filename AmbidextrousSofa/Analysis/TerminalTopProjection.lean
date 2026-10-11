module

public import AmbidextrousSofa.Analysis.PartialHorizontalMoment
public import AmbidextrousSofa.Analysis.TerminalCorner

@[expose] public section

/-!
# The actual terminal top-projection bound

Top overhangs are measured from the actual left and right supporting
endpoints at the horizontal top. The proper horizontal source inequality
bounds positive-barrier length by the charged exterior length remaining
after these top pieces are removed. The actual outgoing wall is positive
to the left of its actual zero, which yields the terminal projection
inequality with both physical overhangs retained. A negative middle slope
has no right top overhang.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def topOverhangLeft (U : Set Plane) : ℝ :=
  max (horizontalLeft U + capWidth U / 4 - (MovingSofaOptimality.vplus U (Real.pi / 2)).1) 0

def topOverhangRight (U : Set Plane) : ℝ :=
  max ((MovingSofaOptimality.vminus U (Real.pi / 2)).1 - (horizontalRight U - capWidth U / 4)) 0

theorem topOverhangLeft_nonneg (U : Set Plane) : 0 ≤ topOverhangLeft U := le_max_right _ _

theorem topOverhangRight_nonneg (U : Set Plane) : 0 ≤ topOverhangRight U := le_max_right _ _

theorem real_left_window_without_top_le {l a s t : ℝ}
    (hla : l ≤ a) (hls : l ≤ s) (hat : a ≤ t) :
    volume.real (Icc l a \ Ioo s t) ≤ min a s - l := by
  refine (measureReal_mono (s₂ := insert a (Icc l (min a s))) (fun x hx => ?_)
    (isCompact_Icc.insert a).measure_ne_top).trans_eq ?_
  · by_cases hxs : x ≤ s
    · exact .inr ⟨hx.1.1, le_min hx.1.2 hxs⟩
    · exact .inl (le_antisymm hx.1.2 (not_lt.1 fun hxa => hx.2 ⟨not_le.1 hxs, hxa.trans_le hat⟩))
  · rw [measureReal_congr (insert_ae_eq_self _ _), Real.volume_real_Icc_of_le (le_min hla hls)]

theorem real_right_window_without_top_le {b r s t : ℝ}
    (hbr : b ≤ r) (htr : t ≤ r) (hsb : s ≤ b) :
    volume.real (Icc b r \ Ioo s t) ≤ r - max b t := by
  refine (measureReal_mono (s₂ := insert b (Icc (max b t) r)) (fun x hx => ?_)
    (isCompact_Icc.insert b).measure_ne_top).trans_eq ?_
  · by_cases htx : t ≤ x
    · exact .inr ⟨max_le hx.1.1 htx, hx.1.2⟩
    · exact .inl (le_antisymm (not_lt.1 fun hbx => hx.2 ⟨hsb.trans_lt hbx, not_le.1 htx⟩) hx.1.1)
  · rw [measureReal_congr (insert_ae_eq_self _ _), Real.volume_real_Icc_of_le (max_le hbr htr)]

/-- The source bound loses precisely the actual top overhangs from the
two charged windows. A top point in the actual middle interval is supplied
by the proved insertion theorem. -/
theorem IsJointCapMaximizer.positive_partial_middle_measure_le_width_sub_topOverhangs
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      {x : ℝ | 0 < partialBarrier U α x}) ≤
      capWidth U / 2 - topOverhangLeft U - topOverhangRight U := by
  have hK := hU.isCap.imported_isConvexBody
  have hsTop : ((MovingSofaOptimality.vplus U (Real.pi / 2)).1, (1 : ℝ)) ∈ U := by
    rw [← hheight, ← top_vplus_snd_eq_capHeight]
    exact (MovingSofaOptimality.vplus_mem_edge hK _).1
  have htTop : ((MovingSofaOptimality.vminus U (Real.pi / 2)).1, (1 : ℝ)) ∈ U := by
    rw [← hheight, ← top_vminus_snd_eq_capHeight]
    exact (MovingSofaOptimality.vminus_mem_edge hK _).1
  obtain ⟨z, hz, hzTop⟩ := hU.top_meets_middle hheight
  have hzst := hU.isCap.fst_mem_top_face hzTop hheight.symm
  have hW := hU.isCap.capWidth_nonneg
  have hs : horizontalLeft U ≤ (MovingSofaOptimality.vplus U (Real.pi / 2)).1 :=
    csInf_le (isCompact_horizontalProjection hU.isCap.isCompact).bddBelow ⟨_, hsTop, rfl⟩
  have ht : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 ≤ horizontalRight U :=
    le_csSup (isCompact_horizontalProjection hU.isCap.isCompact).bddAbove ⟨_, htTop, rfl⟩
  have hL := real_left_window_without_top_le (a := horizontalLeft U + capWidth U / 4)
    (by linarith) hs (hz.1.trans hzst.2)
  have hR := real_right_window_without_top_le (b := horizontalRight U - capWidth U / 4)
    (by linarith) ht (hzst.1.trans hz.2)
  refine (hU.positive_partial_middle_measure_le_outer_without_top hproper hheight haffine hsTop
    htTop).trans ((add_le_add hL hR).trans_eq ?_)
  have h1 (a s : ℝ) : max (a - s) 0 = a - min a s := by
    rw [← max_sub_sub_left, sub_self, max_comm]
  have h2 (b t : ℝ) : max (t - b) 0 = max b t - b := by
    rw [← max_sub_sub_right, sub_self, max_comm]
  rw [topOverhangLeft, topOverhangRight, h1, h2, capWidth]
  ring

theorem IsJointCapMaximizer.topOverhangRight_eq_zero_of_negative
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : topOverhangRight U = 0 := by
  simp only [topOverhangRight, hU.top_vminus_of_negative_affine_middle hheight hm haffine,
    max_eq_right_iff]
  linarith [hU.isCap.capWidth_nonneg,
    show capWidth U = horizontalRight U - horizontalLeft U from rfl]

/-- The terminal tail abscissa is the right middle endpoint plus its
actual top overhang. A negative middle has no right top overhang and the
tail is its pinned middle endpoint. -/
theorem IsJointCapMaximizer.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (terminalTailPoint U α).1 = horizontalRight U - capWidth U / 4 + topOverhangRight U := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [hU.terminalTailPoint_eq_of_negative hregime hm haffine,
      hU.topOverhangRight_eq_zero_of_negative hheight hm haffine, add_zero]
  have hbound := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).1
  rw [hU.terminalTailPoint_eq_of_nonneg hproper hheight hm haffine] at hbound ⊢
  rw [topOverhangRight, max_eq_left (sub_nonneg.2 hbound)]
  ring

/-- The projection inequality from the actual source limit: the outgoing wall is positive left of
its zero, so the top overhangs fit in the terminal inset. -/
theorem IsJointCapMaximizer.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    topOverhangLeft U + 2 * topOverhangRight U ≤ terminalTailInset U α := by
  have hW : capWidth U = horizontalRight U - horizontalLeft U := rfl
  have htail := hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine
  obtain ⟨hd, hdcos, -⟩ := hU.isCap.terminalTailInset_bounds hU.angle_pos hproper htail.2.1
  have hzero := hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime hregime
    hproper hheight haffine
  have hwide := hU.width_gt_forty_nine_twenty_fifths hproper
  have hcos := (terminal_sin_cos_bounds_after_initialAngle
    hU.terminal_angle_gt_arctan_eight_thirds.le hproper).2
  have hTL := topOverhangLeft_nonneg U
  have hTR := topOverhangRight_nonneg U
  -- The window between the left middle endpoint and the outgoing zero has positive barrier.
  have hlength : min (horizontalRight U - capWidth U / 4)
      ((terminalTailPoint U α).1 - terminalTailInset U α) - (horizontalLeft U + capWidth U / 4) ≤
      capWidth U / 2 - topOverhangLeft U - topOverhangRight U := by
    rw [← Real.volume_real_Ioo_of_le (le_min (by linarith) (by linarith [htail.1]))]
    refine (measureReal_mono (fun x hx => ?_) (measure_ne_top_of_subset inter_subset_left
      measure_Icc_lt_top.ne)).trans (hU.positive_partial_middle_measure_le_width_sub_topOverhangs
        hproper hheight ⟨m, c, haffine⟩)
    exact ⟨⟨hx.1.le, hx.2.le.trans (min_le_left _ _)⟩,
      partialBarrier_pos_of_lt_terminalTailZero U hU.angle_pos hproper
        (hx.2.trans_le (min_le_right _ _))⟩
  rcases min_cases (horizontalRight U - capWidth U / 4)
    ((terminalTailPoint U α).1 - terminalTailInset U α) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [h] at hlength <;> linarith

end AmbidextrousSofa
