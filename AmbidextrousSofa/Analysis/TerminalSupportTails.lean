module

public import AmbidextrousSofa.Analysis.PartialFacetPinning
public import AmbidextrousSofa.Analysis.UnusedCurvature
public import AmbidextrousSofa.Analysis.AxisFaces
public import AmbidextrousSofa.Analysis.TerminalScalar

@[expose] public section

/-!
# Literal support vertices on the unvisited terminal tails

The upward support is the cap height, and every cap point at that height
lies on the top face.

The actual used-support representation has no defining normal in an
unvisited gap, apart from the affine middle normal. The halfplane corner
theorem therefore identifies one actual vertex supporting every angle in
each closed gap. The middle-face endpoints come from the proved partial
insertion variation. No terminal atom is removed by these identities.

The elementary width and height bounds also place the middle normal
strictly before the terminal companion normal. Hence the entire missing
companion tail is supported at the actual upper left projection endpoint.
With a negative middle slope, the right endpoint of the top face is the
left middle endpoint.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- A cap point at the cap height lies on the top face, between its two endpoints. -/
theorem IsDownwardCap.fst_mem_top_face {U : Set Plane} (hU : IsDownwardCap U) {p : Plane}
    (hp : p ∈ U) (hpy : p.2 = capHeight U) :
    p.1 ∈ Icc (MovingSofaOptimality.vplus U (Real.pi / 2)).1
      (MovingSofaOptimality.vminus U (Real.pi / 2)).1 := by
  rw [← hU.horizontalProjection_edge (by simp)]
  exact ⟨p, MovingSofaOptimality.mem_edge_iff.2 ⟨hp, by
    rw [MovingSofaOptimality.dot_uvec_pi_div_two, hpy, imported_supp_pi_div_two]⟩, rfl⟩

theorem support_vertices_of_halfplane_gap {K : Set Plane}
    (hK : MovingSofaOptimality.IsConvexBody K) {ι : Type*} (angle height : ι → ℝ)
    (hpoly : K = ⋂ i, MovingSofaOptimality.halfMinus (angle i) (height i))
    (hangle : ∀ i, angle i ∈ Icc 0 (2 * Real.pi))
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi) (hab : a < b) (hspan : b - a < Real.pi)
    (hgap : ∀ i, angle i ∉ Ioo a b) :
    MovingSofaOptimality.vplus K a = MovingSofaOptimality.vminus K b ∧ ∀ t ∈ Icc a b,
      angleSupport K t = coordDot (MovingSofaOptimality.vminus K b) (unitNormal t) := by
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) hspan
  obtain ⟨q, hq, hqa, hqb⟩ := MovingSofaOptimality.mpc_corner hK hpoly hsin fun i => by
    refine MovingSofaOptimality.mpc_not_gap hab ?_
    rcases le_or_gt (angle i) a with hia | hia
    · exact .inr ⟨by linarith [(hangle i).1, Real.pi_pos], hia⟩
    · exact .inl ⟨not_lt.1 fun hib => hgap i ⟨hia, hib⟩, by linarith [(hangle i).2]⟩
  obtain ⟨hqa, rfl, hsupport, -⟩ := MovingSofaOptimality.mpc_corner_props hK hq hsin hqa hqb
  exact ⟨hqa, fun t ht => (hsupport t (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
    (by linarith [ht.2])) (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2])
    (by linarith [ht.1]))).symm⟩

/-- A gap of normal angles inside the unused intervals that misses the affine middle normal is
supported at one actual vertex. -/
theorem IsJointCapMaximizer.support_vertices_unused_gap
    {U : Set Plane} {α m c a b : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (ha : α ≤ a) (hb : b ≤ Real.pi) (hab : a < b)
    (hunused : Ioo a b ⊆ Ioo α (Real.pi / 2) ∪ Ioo (α + Real.pi / 2) Real.pi)
    (hgap : affineNormalAngle m ∉ Ioo a b) :
    MovingSofaOptimality.vplus U a = MovingSofaOptimality.vminus U b ∧
      ∀ t ∈ Icc a b, angleSupport U t = coordDot (MovingSofaOptimality.vminus U b) (unitNormal t) :=
  support_vertices_of_halfplane_gap hU.isCap.imported_isConvexBody _ _
    ((hU.eq_usedSupportSaturation_capCut haffine).trans
      (capCut_usedSupportSaturation_eq_halfplanes U α m c))
    (FinitePolygon.fullPolygonAngle_mem _ (partialCapAngle_mem hU.angle_mem.2 m))
    (hU.angle_pos.le.trans ha) hb hab (by linarith [hU.angle_pos]) fun i hi =>
    hgap (partialCapAngle_eq_middle_of_mem_unused hU.angle_pos.le hU.angle_mem.2 i
      (hunused hi) ▸ hi)

theorem IsJointCapMaximizer.support_vertices_first_unused_gap
    {U : Set Plane} {α m c a b : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (ha : α ≤ a) (hb : b ≤ Real.pi / 2) (hab : a < b)
    (hgap : affineNormalAngle m ∉ Ioo a b) :
    MovingSofaOptimality.vplus U a = MovingSofaOptimality.vminus U b ∧
      ∀ t ∈ Icc a b, angleSupport U t = coordDot (MovingSofaOptimality.vminus U b) (unitNormal t) :=
  hU.support_vertices_unused_gap haffine ha (by linarith [Real.pi_pos]) hab
    ((Ioo_subset_Ioo ha hb).trans subset_union_left) hgap

theorem IsDownwardCap.edge_affineNormalAngle_eq_supportFace {U : Set Plane}
    (hU : IsDownwardCap U) (m : ℝ) :
    MovingSofaOptimality.edge U (affineNormalAngle m) = supportFace U (-m, 1) := by
  have hc := Real.cos_arctan_pos m
  have hn : unitNormal (affineNormalAngle m) = Real.cos (Real.arctan m) • (-m, 1) := by
    ext <;> simp [unitNormal, affineNormalAngle, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      Real.sin_arctan, Real.cos_arctan]
    ring
  ext p
  change p ∈ U ∧ coordDot p (unitNormal _) = support U (unitNormal _) ↔ _
  rw [hn, support_smul_direction hU.isCompact hU.nonempty _ hc.le, coordDot_smul_right,
    mul_right_inj' hc.ne']
  rfl

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
    rw [← hU.isCap.horizontalProjection_edge hs.le, hU.isCap.edge_affineNormalAngle_eq_supportFace]
    exact hU.horizontalProjection_middle_supportFace hm haffine
  have hends := (Icc_eq_Icc_iff (hU.isCap.face_fst_order hs.le)).mp hproj
  have hK := hU.isCap.imported_isConvexBody
  exact ⟨Prod.ext hends.1 (by simpa only [hends.1, capWidth] using
      hU.isCap.capRoof_eq_of_mem_upper_edge hs (MovingSofaOptimality.vplus_mem_edge hK _)),
    Prod.ext hends.2 (by simpa only [hends.2, capWidth] using
      hU.isCap.capRoof_eq_of_mem_upper_edge hs (MovingSofaOptimality.vminus_mem_edge hK _))⟩

/-- The actual affine middle normal is strictly below the companion
terminal normal, by the width bound and the outgoing-wall angle exclusion. -/
theorem IsJointCapMaximizer.middle_normal_lt_terminal_companion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : affineNormalAngle m < α + Real.pi / 2 := by
  have hW : (8 / 5 : ℝ) < capWidth U := eight_fifths_lt_M.trans_le hU.width_bounds.1
  obtain ⟨-, -, hab⟩ := hU.isCap.middleChord_endpoints (by linarith : 0 < capWidth U)
  have := haffine _ ⟨le_rfl, hab.le⟩
  have := haffine _ ⟨hab.le, le_rfl⟩
  have := capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1)
    (horizontalLeft U + capWidth U / 4)
  have := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip (horizontalRight U - capWidth U / 4)
  have hm : m < 5 / 4 := by unfold capWidth at *; nlinarith
  unfold affineNormalAngle
  linarith [Real.arctan_strictMono hm, hU.terminal_angle_gt_arctan_five_fourths]

theorem IsJointCapMaximizer.terminal_companion_vplus
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    MovingSofaOptimality.vplus U (α + Real.pi / 2) =
      (horizontalLeft U, capRoof U (horizontalLeft U)) :=
  (hU.support_vertices_unused_gap haffine (by linarith [Real.pi_pos]) le_rfl (by linarith)
    subset_union_right fun h =>
      lt_asymm h.1 (hU.middle_normal_lt_terminal_companion haffine)).1.trans
    hU.isCap.axis_vminus_pi

/-- Every missing second support, including the terminal support value,
is attained at the actual upper left endpoint of the projection. -/
theorem IsJointCapMaximizer.companion_tail_support
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) {t : ℝ} (ht : t ∈ Icc α (Real.pi / 2)) :
    support U (companionNormal t) =
      -horizontalLeft U * Real.sin t + capRoof U (horizontalLeft U) * Real.cos t := by
  have h := (hU.support_vertices_unused_gap haffine (by linarith [Real.pi_pos]) le_rfl
    (by linarith) subset_union_right fun h =>
      lt_asymm h.1 (hU.middle_normal_lt_terminal_companion haffine)).2 (t + Real.pi / 2)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [hU.isCap.axis_vminus_pi] at h
  rw [companionNormal_eq_unitNormal]
  refine h.trans ?_
  simp [coordDot, unitNormal, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]

theorem IsJointCapMaximizer.first_tail_support_before_middle
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hαm : α < affineNormalAngle m) {t : ℝ} (ht : t ∈ Icc α (affineNormalAngle m)) :
    angleSupport U t = (horizontalRight U - capWidth U / 4) * Real.cos t +
      capRoof U (horizontalRight U - capWidth U / 4) * Real.sin t := by
  have h := (hU.support_vertices_first_unused_gap haffine le_rfl
    (by simpa [affineNormalAngle] using hm.le) hαm (by simp)).2 t ht
  rwa [(hU.middle_support_vertices hm.ne haffine).2] at h

/-- With a negative middle slope, the right endpoint of the top face is the left middle
endpoint. -/
theorem IsJointCapMaximizer.top_vminus_of_negative_affine_middle
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    MovingSofaOptimality.vminus U (Real.pi / 2) = (horizontalLeft U + capWidth U / 4, 1) := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith [hU.width_bounds.1, one_lt_M])
  have hfa := hU.middle_left_eq_one_of_affine_nonpos hheight hm.le haffine
  have htop : (horizontalLeft U + capWidth U / 4, (1 : ℝ)) ∈ U :=
    hfa ▸ capRoof_mem hU.isCap.isCompact ha
  have hv := MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)
  have hle : horizontalLeft U + capWidth U / 4 ≤ _ :=
    (hU.isCap.fst_mem_top_face htop hheight.symm).2
  have := hU.isCap.capRoof_le_affine_of_affine_segment ha hb hab haffine _ ⟨_, hv.1, rfl⟩
  have := hU.isCap.capRoof_eq_of_mem_upper_edge (by simp) hv
  have := haffine (horizontalLeft U + capWidth U / 4) ⟨le_rfl, hab.le⟩
  have : (MovingSofaOptimality.vminus U (Real.pi / 2)).2 = 1 := by
    rw [← MovingSofaOptimality.dot_uvec_pi_div_two, MovingSofaOptimality.dot_vminus_uvec,
      imported_supp_pi_div_two, hheight]
  exact Prod.ext (le_antisymm (by nlinarith) hle) this

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
  split_ifs with htm
  · exact hU.first_tail_support_before_middle hm haffine (ht.1.trans_lt htm) ⟨ht.1, htm.le⟩
  have h := (hU.support_vertices_first_unused_gap haffine (le_max_left _ _) le_rfl
    (max_lt hαL (by simpa [affineNormalAngle] using hm)) fun hs =>
      (le_max_right α _).not_gt hs.1).2 t ⟨max_le ht.1 (not_lt.1 htm), ht.2⟩
  rw [hU.top_vminus_of_negative_affine_middle hheight hm haffine] at h
  simpa [coordDot, unitNormal] using h

end AmbidextrousSofa
