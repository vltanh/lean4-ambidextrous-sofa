import AmbidextrousSofa.Analysis.PartialHorizontalMoment
import AmbidextrousSofa.Analysis.TerminalCorner

/-!
# The actual terminal top-projection bound

Top overhangs are measured from the actual left and right supporting
endpoints at the horizontal top. The proper horizontal source inequality
bounds positive-barrier length by the charged exterior length remaining
after these top pieces are removed. The actual outgoing wall is positive
to the left of its actual zero, which yields the terminal projection
inequality with both physical overhangs retained.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def topOverhangLeft (U : Set Plane) : ℝ :=
  max (horizontalLeft U + capWidth U / 4 - (Imported.vplus U (Real.pi / 2)).1) 0

def topOverhangRight (U : Set Plane) : ℝ :=
  max ((Imported.vminus U (Real.pi / 2)).1 - (horizontalRight U - capWidth U / 4)) 0

theorem topOverhangLeft_nonneg (U : Set Plane) : 0 ≤ topOverhangLeft U := le_max_right _ _

theorem topOverhangRight_nonneg (U : Set Plane) : 0 ≤ topOverhangRight U := le_max_right _ _

theorem real_left_window_without_top_le {l a s t : ℝ}
    (hla : l ≤ a) (hls : l ≤ s) (hat : a ≤ t) :
    volume.real (Icc l a \ Ioo s t) ≤ min a s - l := by
  have hsub : Icc l a \ Ioo s t ⊆ Icc l (min a s) ∪ {a} := by
    intro x hx
    by_cases hxs : x ≤ s
    · exact Or.inl ⟨hx.1.1, le_min hx.1.2 hxs⟩
    · right
      apply mem_singleton_iff.mpr
      apply le_antisymm hx.1.2
      by_contra hxa
      exact hx.2 ⟨lt_of_not_ge hxs, (lt_of_not_ge hxa).trans_le hat⟩
  have hfinite : volume (Icc l (min a s) ∪ {a}) ≠ ⊤ := by
    apply (measure_union_lt_top ?_ ?_).ne
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    · simp
  have h := (measureReal_mono hsub hfinite).trans
    (measureReal_union_le (Icc l (min a s)) {a})
  simpa only [Real.volume_real_Icc_of_le (le_min hla hls), Measure.real,
    measure_singleton, ENNReal.toReal_zero, add_zero] using h

theorem real_right_window_without_top_le {b r s t : ℝ}
    (hbr : b ≤ r) (htr : t ≤ r) (hsb : s ≤ b) :
    volume.real (Icc b r \ Ioo s t) ≤ r - max b t := by
  have hsub : Icc b r \ Ioo s t ⊆ Icc (max b t) r ∪ {b} := by
    intro x hx
    by_cases htx : t ≤ x
    · exact Or.inl ⟨max_le hx.1.1 htx, hx.1.2⟩
    · right
      apply mem_singleton_iff.mpr
      apply le_antisymm _ hx.1.1
      by_contra hbx
      exact hx.2 ⟨hsb.trans_lt (lt_of_not_ge hbx), lt_of_not_ge htx⟩
  have hfinite : volume (Icc (max b t) r ∪ {b}) ≠ ⊤ := by
    apply (measure_union_lt_top ?_ ?_).ne
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    · simp
  have h := (measureReal_mono hsub hfinite).trans
    (measureReal_union_le (Icc (max b t) r) {b})
  simpa only [Real.volume_real_Icc_of_le (max_le hbr htr), Measure.real,
    measure_singleton, ENNReal.toReal_zero, add_zero] using h

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
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  let s := (Imported.vplus U (Real.pi / 2)).1
  let t := (Imported.vminus U (Real.pi / 2)).1
  have hp := Imported.vplus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)
  have hq := Imported.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)
  have hpy : (Imported.vplus U (Real.pi / 2)).2 = 1 := by
    have h : coordDot (Imported.vplus U (Real.pi / 2)) (unitNormal (Real.pi / 2)) =
        angleSupport U (Real.pi / 2) := Imported.dot_vplus_uvec U (Real.pi / 2)
    have hy : (Imported.vplus U (Real.pi / 2)).2 = capHeight U := by
      simpa only [coordDot, unitNormal, angleSupport, capHeight,
        Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add] using h
    exact hy.trans hheight
  have hqy : (Imported.vminus U (Real.pi / 2)).2 = 1 :=
    (top_vminus_snd_eq_capHeight U).trans hheight
  have hsTop : (s, 1) ∈ U := by simpa only [s, ← hpy, Prod.mk.eta] using hp.1
  have htTop : (t, 1) ∈ U := by simpa only [t, ← hqy, Prod.mk.eta] using hq.1
  have hsBound : s ∈ Icc (horizontalLeft U) (horizontalRight U) := by
    rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    exact ⟨(s, 1), hsTop, rfl⟩
  have htBound : t ∈ Icc (horizontalLeft U) (horizontalRight U) := by
    rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    exact ⟨(t, 1), htTop, rfl⟩
  obtain ⟨z, hz, hzTop⟩ := hU.top_meets_middle hheight
  have hzEdge : (z, (1 : ℝ)) ∈ Imported.edge U (Real.pi / 2) := by
    refine ⟨hzTop, ?_⟩
    change coordDot (z, 1) (unitNormal (Real.pi / 2)) = angleSupport U (Real.pi / 2)
    simp only [coordDot, unitNormal, angleSupport, Real.cos_pi_div_two,
      Real.sin_pi_div_two, mul_zero, mul_one, zero_add, ← capHeight, hheight]
  have hzst : z ∈ Icc s t := by
    rw [← hU.isCap.horizontalProjection_edge (by simp : 0 ≤ Real.sin (Real.pi / 2))]
    exact ⟨(z, 1), hzEdge, rfl⟩
  have hla : horizontalLeft U ≤ a := by
    dsimp [a]
    linarith [hU.isCap.capWidth_nonneg]
  have hbr : b ≤ horizontalRight U := by
    dsimp [b]
    linarith [hU.isCap.capWidth_nonneg]
  have hat : a ≤ t := hz.1.trans hzst.2
  have hsb : s ≤ b := hzst.1.trans hz.2
  have hmoment := hU.positive_partial_middle_measure_le_outer_without_top
    hproper hheight haffine hsTop htTop
  have hL := real_left_window_without_top_le hla hsBound.1 hat
  have hR := real_right_window_without_top_le hbr htBound.2 hsb
  have hmin : min a s = a - max (a - s) 0 := by
    by_cases h : s ≤ a
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_left (le_of_not_ge h), max_eq_right (by linarith : a - s ≤ 0)]
      ring
  have hmax : max b t = b + max (t - b) 0 := by
    by_cases h : b ≤ t
    · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [max_eq_left (le_of_not_ge h), max_eq_right (by linarith : t - b ≤ 0)]
      ring
  have hsum : min a s - horizontalLeft U + (horizontalRight U - max b t) =
      capWidth U / 2 - topOverhangLeft U - topOverhangRight U := by
    rw [hmin, hmax]
    dsimp [a, b, s, t, topOverhangLeft, topOverhangRight, capWidth]
    ring
  exact (hmoment.trans (add_le_add hL hR)).trans_eq hsum

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
  by_cases hm : m < 0
  · have hαm := (hU.negative_remaining_tail_geometry_of_tail_regime hregime hproper hheight hm haffine).1
    have hmL : affineNormalAngle m < Real.pi / 2 := by
      have h := Real.arctan_lt_zero.mpr hm
      unfold affineNormalAngle
      linarith
    have hv := (hU.support_vertices_first_unused_gap haffine le_rfl hmL.le hαm
      (show affineNormalAngle m ∉ Ioo α (affineNormalAngle m) by simp)).1.trans
      (hU.middle_support_vertices hm.ne haffine).2
    have htop := hU.top_vminus_of_negative_affine_middle hheight hm haffine
    have hneg : horizontalLeft U + capWidth U / 4 -
        (horizontalRight U - capWidth U / 4) ≤ 0 := by
      have hwidth := hU.isCap.capWidth_nonneg
      unfold capWidth at *
      linarith
    unfold terminalTailPoint topOverhangRight
    rw [hv, htop]
    simp only [max_eq_right hneg, add_zero]
  · have hv := hU.first_terminal_vplus_of_middle_nonneg hproper (le_of_not_gt hm) haffine
    have hbound := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).1
    change horizontalRight U - capWidth U / 4 ≤ (Imported.vplus U α).1 at hbound
    rw [hv] at hbound
    unfold terminalTailPoint topOverhangRight
    rw [hv, max_eq_left (sub_nonneg.mpr hbound)]
    ring

theorem IsJointCapMaximizer.terminalTailPoint_fst_eq_middle_add_topOverhangRight
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (terminalTailPoint U α).1 = horizontalRight U - capWidth U / 4 + topOverhangRight U := by
  exact IsJointCapMaximizer.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine

/-- TP's projection inequality is derived from the actual source limit.
The outgoing zero lies strictly inside the middle interval, and both top
overhangs satisfy the displayed weighted bound. -/
theorem IsJointCapMaximizer.terminal_top_projection_bound_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    topOverhangLeft U + 2 * topOverhangRight U ≤ terminalTailInset U α ∧
      topOverhangRight U < terminalTailInset U α ∧
      horizontalLeft U + capWidth U / 4 < terminalTailZero U α ∧
      terminalTailZero U α < horizontalRight U - capWidth U / 4 := by
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  let z := terminalTailZero U α
  let d := terminalTailInset U α
  let P := middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
    {x : ℝ | 0 < partialBarrier U α x}
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hab : a < b := by dsimp [a, b]; unfold capWidth at *; linarith
  have hwidth : b - a = capWidth U / 2 := by dsimp [a, b, capWidth]; ring
  have htail := hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine
  obtain ⟨hdpos, hdcos, _, _, _⟩ :=
    hU.isCap.terminalTailInset_bounds hU.angle_pos hproper htail.2.1
  have hzero : z = b + topOverhangRight U - d := by
    dsimp [z, terminalTailZero]
    rw [hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime hregime hproper hheight haffine]
    rfl
  have hwide := hU.width_gt_forty_nine_twenty_fifths hproper
  have hcos := (terminal_sin_cos_bounds_after_initialAngle
    hU.terminal_angle_gt_arctan_eight_thirds.le hproper).2
  have haz : a < z := by
    have hleftTail : b ≤ (terminalTailPoint U α).1 := htail.1
    dsimp [z, terminalTailZero]
    linarith only [hleftTail, hdcos, hcos, hwide, hwidth]
  have hmin : a ≤ min b z := le_min hab.le haz.le
  have hsubset : Ioo a (min b z) ⊆ P := by
    intro x hx
    refine ⟨⟨hx.1.le, hx.2.le.trans (min_le_left _ _)⟩, ?_⟩
    exact partialBarrier_pos_of_lt_terminalTailZero U hU.angle_pos hproper
      (hx.2.trans_le (min_le_right _ _))
  have hlength : min b z - a ≤ volume.real P := by
    rw [← Real.volume_real_Ioo_of_le hmin]
    apply measureReal_mono hsubset
    exact measure_ne_top_of_subset inter_subset_left (by
      change volume (Icc a b) ≠ ⊤
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hmoment := hU.positive_partial_middle_measure_le_width_sub_topOverhangs
    hproper hheight ⟨m, c, haffine⟩
  change volume.real P ≤ capWidth U / 2 - topOverhangLeft U - topOverhangRight U at hmoment
  have hbound := hlength.trans hmoment
  have hT0 := topOverhangLeft_nonneg U
  have hR0 := topOverhangRight_nonneg U
  have hRd : topOverhangRight U < d := by
    by_contra h
    have hdR : d ≤ topOverhangRight U := le_of_not_gt h
    have hbz : b ≤ z := by linarith only [hzero, hdR]
    rw [min_eq_left hbz] at hbound
    change 0 < d at hdpos
    linarith only [hbound, hwidth, hT0, hdR, hdpos]
  have hzb : z < b := by linarith only [hzero, hRd]
  rw [min_eq_right hzb.le] at hbound
  refine ⟨?_, hRd, haz, hzb⟩
  change topOverhangLeft U + 2 * topOverhangRight U ≤ d
  linarith only [hbound, hwidth, hzero]

theorem IsJointCapMaximizer.terminal_top_projection_bound
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    topOverhangLeft U + 2 * topOverhangRight U ≤ terminalTailInset U α ∧
      topOverhangRight U < terminalTailInset U α ∧
      horizontalLeft U + capWidth U / 4 < terminalTailZero U α ∧
      terminalTailZero U α < horizontalRight U - capWidth U / 4 := by
  exact IsJointCapMaximizer.terminal_top_projection_bound_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine

theorem IsJointCapMaximizer.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    topOverhangLeft U + 2 * topOverhangRight U ≤ terminalTailInset U α :=
  (hU.terminal_top_projection_bound_of_tail_regime hregime hproper hheight haffine).1

theorem IsJointCapMaximizer.topOverhangLeft_add_twice_right_le_terminalInset
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    topOverhangLeft U + 2 * topOverhangRight U ≤ terminalTailInset U α := by
  exact IsJointCapMaximizer.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine

end AmbidextrousSofa
