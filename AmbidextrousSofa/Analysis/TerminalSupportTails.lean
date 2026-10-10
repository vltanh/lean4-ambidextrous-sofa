module

public import AmbidextrousSofa.Analysis.PartialFacetPinning
public import AmbidextrousSofa.Analysis.UnusedCurvature
public import AmbidextrousSofa.Analysis.AxisFaces
public import AmbidextrousSofa.Analysis.TerminalScalar

@[expose] public section

/-!
# Literal support vertices on the unvisited terminal tails

The actual used-support representation has no defining normal in an
unvisited gap, apart from the affine middle normal. The halfplane corner
theorem therefore identifies one actual vertex supporting every angle in
each closed gap. The middle-face endpoints come from the proved partial
insertion variation. No terminal atom is removed by these identities.

The elementary width and height bounds also place the middle normal
strictly before the terminal companion normal. Hence the entire missing
companion tail is supported at the actual upper left projection endpoint.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem support_vertices_of_halfplane_gap {K : Set Plane}
    (hK : MovingSofaOptimality.IsConvexBody K) {ι : Type*} (angle height : ι → ℝ)
    (hpoly : K = ⋂ i, MovingSofaOptimality.halfMinus (angle i) (height i))
    (hangle : ∀ i, angle i ∈ Icc 0 (2 * Real.pi))
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi) (hab : a < b) (hspan : b - a < Real.pi)
    (hgap : ∀ i, angle i ∉ Ioo a b) :
    MovingSofaOptimality.vplus K a = MovingSofaOptimality.vminus K b ∧
      (∀ t ∈ Icc a b, angleSupport K t = coordDot (MovingSofaOptimality.vminus K b) (unitNormal t)) ∧
      (∀ t ∈ Ioo a b, MovingSofaOptimality.vplus K t = MovingSofaOptimality.vminus K b ∧
        MovingSofaOptimality.vminus K t = MovingSofaOptimality.vminus K b) := by
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) hspan
  have hsinGap : ∀ i, ¬(0 < Real.sin (angle i - a) ∧ Real.sin (angle i - b) < 0) := by
    intro i
    apply MovingSofaOptimality.mpc_not_gap hab
    by_cases hia : angle i ≤ a
    · right
      exact ⟨by linarith [(hangle i).1, Real.pi_pos], hia⟩
    · have hai : a < angle i := lt_of_not_ge hia
      have hbi : b ≤ angle i := le_of_not_gt (fun hib => hgap i ⟨hai, hib⟩)
      left
      exact ⟨hbi, by linarith [(hangle i).2]⟩
  obtain ⟨q, hq, hqa, hqb⟩ := MovingSofaOptimality.mpc_corner hK hpoly hsin hsinGap
  obtain ⟨hqaVertex, hqbVertex, hsupport, hinterior⟩ :=
    MovingSofaOptimality.mpc_corner_props hK hq hsin hqa hqb
  refine ⟨hqaVertex.trans hqbVertex.symm, ?_, ?_⟩
  · intro t ht
    rw [hqbVertex]
    exact (hsupport t
      (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.1) (by linarith [ht.2]))
      (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2) (by linarith [ht.1]))).symm
  · intro t ht
    have h := hinterior t
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr ht.1) (by linarith [ht.2]))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr ht.2) (by linarith [ht.1]))
    exact ⟨h.1.trans hqbVertex.symm, h.2.trans hqbVertex.symm⟩

theorem IsJointCapMaximizer.support_vertices_first_unused_gap
    {U : Set Plane} {α m c a b : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (ha : α ≤ a) (hb : b ≤ Real.pi / 2) (hab : a < b)
    (hgap : affineNormalAngle m ∉ Ioo a b) :
    MovingSofaOptimality.vplus U a = MovingSofaOptimality.vminus U b ∧
      (∀ t ∈ Icc a b, angleSupport U t = coordDot (MovingSofaOptimality.vminus U b) (unitNormal t)) ∧
      (∀ t ∈ Ioo a b, MovingSofaOptimality.vplus U t = MovingSofaOptimality.vminus U b ∧
        MovingSofaOptimality.vminus U t = MovingSofaOptimality.vminus U b) := by
  let angle := FinitePolygon.fullPolygonAngle (partialCapAngle α m)
  let height := FinitePolygon.fullPolygonHeight (horizontalLeft U) (horizontalRight U)
    (partialCapHeight U α m c)
  have hpoly : U = ⋂ i, MovingSofaOptimality.halfMinus (angle i) (height i) :=
    (hU.eq_usedSupportSaturation_capCut haffine).trans
      (capCut_usedSupportSaturation_eq_halfplanes U α m c)
  apply support_vertices_of_halfplane_gap hU.isCap.imported_isConvexBody angle height hpoly
    (FinitePolygon.fullPolygonAngle_mem _ (partialCapAngle_mem hU.angle_mem.2 m))
    (hU.angle_pos.le.trans ha) (by linarith [Real.pi_pos]) hab
    (by linarith [hU.angle_pos])
  intro i hi
  have heq : angle i = affineNormalAngle m :=
    partialCapAngle_eq_middle_of_mem_unused hU.angle_pos.le hU.angle_mem.2 i
      (Or.inl ⟨ha.trans_lt hi.1, hi.2.trans_le hb⟩)
  exact hgap (heq ▸ hi)

theorem IsJointCapMaximizer.support_vertices_companion_unused_gap
    {U : Set Plane} {α m c a b : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (ha : α + Real.pi / 2 ≤ a) (hb : b ≤ Real.pi) (hab : a < b)
    (hgap : affineNormalAngle m ∉ Ioo a b) :
    MovingSofaOptimality.vplus U a = MovingSofaOptimality.vminus U b ∧
      (∀ t ∈ Icc a b, angleSupport U t = coordDot (MovingSofaOptimality.vminus U b) (unitNormal t)) ∧
      (∀ t ∈ Ioo a b, MovingSofaOptimality.vplus U t = MovingSofaOptimality.vminus U b ∧
        MovingSofaOptimality.vminus U t = MovingSofaOptimality.vminus U b) := by
  let angle := FinitePolygon.fullPolygonAngle (partialCapAngle α m)
  let height := FinitePolygon.fullPolygonHeight (horizontalLeft U) (horizontalRight U)
    (partialCapHeight U α m c)
  have hpoly : U = ⋂ i, MovingSofaOptimality.halfMinus (angle i) (height i) :=
    (hU.eq_usedSupportSaturation_capCut haffine).trans
      (capCut_usedSupportSaturation_eq_halfplanes U α m c)
  apply support_vertices_of_halfplane_gap hU.isCap.imported_isConvexBody angle height hpoly
    (FinitePolygon.fullPolygonAngle_mem _ (partialCapAngle_mem hU.angle_mem.2 m))
    (by linarith [hU.angle_pos, Real.pi_pos]) hb hab
    (by linarith [hU.angle_pos, Real.pi_pos])
  intro i hi
  have heq : angle i = affineNormalAngle m :=
    partialCapAngle_eq_middle_of_mem_unused hU.angle_pos.le hU.angle_mem.2 i
      (Or.inr ⟨ha.trans_lt hi.1, hi.2.trans_le hb⟩)
  exact hgap (heq ▸ hi)

theorem unitNormal_affineNormalAngle (m : ℝ) :
    unitNormal (affineNormalAngle m) = Real.cos (Real.arctan m) • (-m, 1) := by
  have hs : Real.sin (Real.arctan m) = m * Real.cos (Real.arctan m) := by
    have h := Real.tan_arctan m
    rwa [Real.tan_eq_sin_div_cos, div_eq_iff (Real.cos_arctan_pos m).ne'] at h
  apply Prod.ext
  · change Real.cos (Real.arctan m + Real.pi / 2) = Real.cos (Real.arctan m) * (-m)
    rw [Real.cos_add_pi_div_two, hs]
    ring
  · change Real.sin (Real.arctan m + Real.pi / 2) = Real.cos (Real.arctan m) * 1
    rw [Real.sin_add_pi_div_two, mul_one]

theorem IsDownwardCap.edge_affineNormalAngle_eq_supportFace {U : Set Plane}
    (hU : IsDownwardCap U) (m : ℝ) :
    MovingSofaOptimality.edge U (affineNormalAngle m) = supportFace U (-m, 1) := by
  ext p
  change (p ∈ U ∧ coordDot p (unitNormal (affineNormalAngle m)) =
      support U (unitNormal (affineNormalAngle m))) ↔
    p ∈ U ∧ coordDot p (-m, 1) = support U (-m, 1)
  rw [unitNormal_affineNormalAngle,
    support_smul_direction hU.isCompact hU.nonempty _ (Real.cos_arctan_pos m).le,
    coordDot_smul_right]
  constructor
  · rintro ⟨hp, heq⟩
    exact ⟨hp, mul_left_cancel₀ (Real.cos_arctan_pos m).ne' heq⟩
  · rintro ⟨hp, heq⟩
    exact ⟨hp, congrArg (fun v => Real.cos (Real.arctan m) * v) heq⟩

/-- Both endpoints belong to the actual middle face and are exactly its
left and right roof endpoints; the nonzero slope can have either sign. -/
theorem IsJointCapMaximizer.middle_support_vertices
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α) (hm : m ≠ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    MovingSofaOptimality.vplus U (affineNormalAngle m) =
      (horizontalLeft U + capWidth U / 4, capRoof U (horizontalLeft U + capWidth U / 4)) ∧
    MovingSofaOptimality.vminus U (affineNormalAngle m) =
      (horizontalRight U - capWidth U / 4, capRoof U (horizontalRight U - capWidth U / 4)) := by
  have hs : 0 < Real.sin (affineNormalAngle m) :=
    Real.sin_pos_of_pos_of_lt_pi (affineNormalAngle_mem m).1 (affineNormalAngle_mem m).2
  have hproj : Icc (MovingSofaOptimality.vplus U (affineNormalAngle m)).1
      (MovingSofaOptimality.vminus U (affineNormalAngle m)).1 =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
    rw [← hU.isCap.horizontalProjection_edge hs.le,
      hU.isCap.edge_affineNormalAngle_eq_supportFace]
    exact hU.horizontalProjection_middle_supportFace hm haffine
  have hends := (Icc_eq_Icc_iff (hU.isCap.face_fst_order hs.le)).mp hproj
  constructor
  · apply Prod.ext hends.1
    have h := hU.isCap.capRoof_eq_of_mem_upper_edge hs
      (MovingSofaOptimality.vplus_mem_edge hU.isCap.imported_isConvexBody (affineNormalAngle m))
    simpa only [hends.1] using h
  · apply Prod.ext hends.2
    have h := hU.isCap.capRoof_eq_of_mem_upper_edge hs
      (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (affineNormalAngle m))
    simpa only [hends.2] using h

theorem IsJointCapMaximizer.middle_slope_lt_five_fourths
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : m < (5 / 4 : ℝ) := by
  have hwidth : (8 / 5 : ℝ) < capWidth U := eight_fifths_lt_M.trans_le hU.width_bounds.1
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints (by linarith : 0 < capWidth U)
  have hfa := haffine (horizontalLeft U + capWidth U / 4) ⟨le_rfl, hab.le⟩
  have hfb := haffine (horizontalRight U - capWidth U / 4) ⟨hab.le, le_rfl⟩
  have ha0 := capRoof_nonneg hU.isCap.isCompact
    (fun p hp => (hU.isCap.inStrip hp).1) (horizontalLeft U + capWidth U / 4)
  have hb1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip
    (horizontalRight U - capWidth U / 4)
  have hproduct : m * capWidth U ≤ 2 := by
    unfold capWidth at *
    nlinarith
  by_contra hm
  have hm0 : (5 / 4 : ℝ) ≤ m := le_of_not_gt hm
  have h := mul_lt_mul_of_pos_left hwidth (show 0 < m by linarith)
  nlinarith

/-- The actual affine middle normal is strictly below the companion
terminal normal. This follows from the width bound and the already proved
outgoing-wall angle exclusion, without a source-density assumption. -/
theorem IsJointCapMaximizer.middle_normal_lt_terminal_companion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : affineNormalAngle m < α + Real.pi / 2 := by
  have hm := Real.arctan_strictMono (hU.middle_slope_lt_five_fourths haffine)
  have hα := hU.terminal_angle_gt_arctan_five_fourths
  unfold affineNormalAngle
  linarith

theorem IsJointCapMaximizer.terminal_companion_vplus
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    MovingSofaOptimality.vplus U (α + Real.pi / 2) =
      (horizontalLeft U, capRoof U (horizontalLeft U)) := by
  have hm := hU.middle_normal_lt_terminal_companion haffine
  have h := hU.support_vertices_companion_unused_gap haffine le_rfl le_rfl
    (show α + Real.pi / 2 < Real.pi by linarith)
    (show affineNormalAngle m ∉ Ioo (α + Real.pi / 2) Real.pi by
      intro ht; linarith [ht.1])
  exact h.1.trans hU.isCap.axis_vminus_pi

/-- Every missing second support, including the terminal support value,
is attained at the actual upper left endpoint of the projection. The
possible face on the terminal normal itself is not collapsed here. -/
theorem IsJointCapMaximizer.companion_tail_support
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) {t : ℝ} (ht : t ∈ Icc α (Real.pi / 2)) :
    support U (companionNormal t) =
      -horizontalLeft U * Real.sin t + capRoof U (horizontalLeft U) * Real.cos t := by
  have hm := hU.middle_normal_lt_terminal_companion haffine
  have h := hU.support_vertices_companion_unused_gap haffine le_rfl le_rfl
    (show α + Real.pi / 2 < Real.pi by linarith)
    (show affineNormalAngle m ∉ Ioo (α + Real.pi / 2) Real.pi by
      intro hs; linarith [hs.1])
  have hsupport := h.2.1 (t + Real.pi / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [hU.isCap.axis_vminus_pi] at hsupport
  change support U (unitNormal (t + Real.pi / 2)) =
    coordDot (horizontalLeft U, capRoof U (horizontalLeft U))
      (unitNormal (t + Real.pi / 2)) at hsupport
  simp only [← companionNormal_eq_unitNormal] at hsupport
  simpa only [coordDot, companionNormal, mul_neg, neg_mul] using hsupport

theorem IsJointCapMaximizer.first_tail_support_before_middle
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hαm : α < affineNormalAngle m) {t : ℝ} (ht : t ∈ Icc α (affineNormalAngle m)) :
    angleSupport U t = (horizontalRight U - capWidth U / 4) * Real.cos t +
      capRoof U (horizontalRight U - capWidth U / 4) * Real.sin t := by
  have hmL : affineNormalAngle m < Real.pi / 2 := by
    have h := Real.arctan_lt_zero.mpr hm
    unfold affineNormalAngle
    linarith
  have h := hU.support_vertices_first_unused_gap haffine le_rfl hmL.le hαm
    (show affineNormalAngle m ∉ Ioo α (affineNormalAngle m) by simp)
  have hv := (hU.middle_support_vertices hm.ne haffine).2
  have hsupport := h.2.1 t ht
  rw [hv] at hsupport
  exact hsupport

theorem IsDownwardCap.top_vminus_of_negative_affine_segment
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hm : m < 0)
    (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hfa : capRoof U a = 1) : MovingSofaOptimality.vminus U (Real.pi / 2) = (a, 1) := by
  have htop : (a, (1 : ℝ)) ∈ U := by
    rw [← hfa]
    exact capRoof_mem hU.isCompact ha
  have hHeight : angleSupport U (Real.pi / 2) = 1 := by
    apply support_eq_of_mem hU.isCompact (q := (a, 1)) ?_ htop ?_
    · intro p hp
      simpa only [coordDot, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
        mul_zero, mul_one, zero_add] using (hU.inStrip hp).2
    · simp only [coordDot, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
        mul_zero, mul_one, zero_add]
  have hp := MovingSofaOptimality.vminus_mem_edge hU.imported_isConvexBody (Real.pi / 2)
  have hpy : (MovingSofaOptimality.vminus U (Real.pi / 2)).2 = 1 := by
    have h := hp.2
    change coordDot (MovingSofaOptimality.vminus U (Real.pi / 2)) (unitNormal (Real.pi / 2)) =
      angleSupport U (Real.pi / 2) at h
    rw [hHeight] at h
    simpa only [coordDot, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add] using h
  have htopEdge : (a, (1 : ℝ)) ∈ MovingSofaOptimality.edge U (Real.pi / 2) := by
    refine ⟨htop, ?_⟩
    change coordDot (a, 1) (unitNormal (Real.pi / 2)) = angleSupport U (Real.pi / 2)
    rw [hHeight]
    simp only [coordDot, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add]
  have hleft : a ≤ (MovingSofaOptimality.vminus U (Real.pi / 2)).1 := by
    have h := MovingSofaOptimality.dot_vminus_le_dot hU.isCompact htopEdge
    simp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi_div_two, Real.cos_pi_div_two,
      mul_neg, mul_one, mul_zero, add_zero] at h
    linarith
  have hroof : capRoof U (MovingSofaOptimality.vminus U (Real.pi / 2)).1 = 1 := by
    have h := hU.capRoof_eq_of_mem_upper_edge
      (show 0 < Real.sin (Real.pi / 2) by rw [Real.sin_pi_div_two]; norm_num) hp
    exact h.symm.trans hpy
  have hceiling := hU.capRoof_le_affine_of_affine_segment ha hb hab haffine
    (MovingSofaOptimality.vminus U (Real.pi / 2)).1 ⟨MovingSofaOptimality.vminus U (Real.pi / 2), hp.1, rfl⟩
  rw [hroof] at hceiling
  have hline := haffine a ⟨le_rfl, hab.le⟩
  rw [hfa] at hline
  have hright : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 ≤ a := by
    by_contra h
    have hax := lt_of_not_ge h
    have hmul := mul_lt_mul_of_neg_left hax hm
    linarith
  exact Prod.ext (le_antisymm hright hleft) hpy

theorem IsJointCapMaximizer.top_vminus_of_negative_affine_middle
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    MovingSofaOptimality.vminus U (Real.pi / 2) = (horizontalLeft U + capWidth U / 4, 1) := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith [hU.width_bounds.1, one_lt_M])
  exact hU.isCap.top_vminus_of_negative_affine_segment ha hb hab hm haffine
    (hU.middle_left_eq_one_of_affine_nonpos hheight hm.le haffine)

theorem IsJointCapMaximizer.first_tail_support_after_middle
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) {t : ℝ}
    (ht : t ∈ Icc (max α (affineNormalAngle m)) (Real.pi / 2)) :
    angleSupport U t = (horizontalLeft U + capWidth U / 4) * Real.cos t + Real.sin t := by
  have hmL : affineNormalAngle m < Real.pi / 2 := by
    have h := Real.arctan_lt_zero.mpr hm
    unfold affineNormalAngle
    linarith
  have h := hU.support_vertices_first_unused_gap haffine (le_max_left _ _) le_rfl
    (max_lt hαL hmL)
    (show affineNormalAngle m ∉ Ioo (max α (affineNormalAngle m)) (Real.pi / 2) by
      intro hs
      exact (not_lt_of_ge (le_max_right α (affineNormalAngle m))) hs.1)
  have hsupport := h.2.1 t ht
  rw [hU.top_vminus_of_negative_affine_middle hheight hm haffine] at hsupport
  simpa only [coordDot, unitNormal, one_mul] using hsupport

/-- The actual negative-tilt missing first supports have exactly two
constant support vertices, meeting at the actual affine middle normal. -/
theorem IsJointCapMaximizer.first_tail_support_negative
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) {t : ℝ} (ht : t ∈ Icc α (Real.pi / 2)) :
    angleSupport U t =
      if t < affineNormalAngle m then
        (horizontalRight U - capWidth U / 4) * Real.cos t +
          capRoof U (horizontalRight U - capWidth U / 4) * Real.sin t
      else (horizontalLeft U + capWidth U / 4) * Real.cos t + Real.sin t := by
  by_cases htm : t < affineNormalAngle m
  · rw [if_pos htm]
    exact hU.first_tail_support_before_middle hm haffine (ht.1.trans_lt htm)
      ⟨ht.1, htm.le⟩
  · rw [if_neg htm]
    exact hU.first_tail_support_after_middle hαL hheight hm haffine
      ⟨max_le ht.1 (le_of_not_gt htm), ht.2⟩

theorem IsJointCapMaximizer.first_terminal_vplus_of_no_middle_gap
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hgap : affineNormalAngle m ∉ Ioo α (Real.pi / 2)) :
    MovingSofaOptimality.vplus U α = MovingSofaOptimality.vminus U (Real.pi / 2) :=
  (hU.support_vertices_first_unused_gap haffine le_rfl le_rfl hαL hgap).1

theorem IsJointCapMaximizer.first_terminal_vplus_of_middle_nonneg
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    MovingSofaOptimality.vplus U α = MovingSofaOptimality.vminus U (Real.pi / 2) := by
  apply hU.first_terminal_vplus_of_no_middle_gap hαL haffine
  have hm0 := Real.arctan_nonneg.mpr hm
  intro h
  unfold affineNormalAngle at h
  linarith [h.2]

end AmbidextrousSofa
