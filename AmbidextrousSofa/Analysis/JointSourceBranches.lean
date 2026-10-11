module

public import AmbidextrousSofa.Analysis.JointSourceDensity
public import AmbidextrousSofa.Analysis.PositiveWallContacts

@[expose] public section

/-!
# The four literal branches of the common source measure

Strict wall slack tags a tangent source; equality of the two walls tags
a corner source. The four measures below are restrictions of the same
selected joint measure. Their partition is proved from its actual
positive wall contacts. No separate choice of a first or companion
occupation measure is made.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def firstSourceSlice : Set Plane := {z | z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2)}

def secondSourceSlice : Set Plane := {z | z.1 ∈ Ioo (Real.pi / 2) Real.pi}

def firstTangentSource (U : Set Plane) : Set Plane :=
  firstSourceSlice ∩ {z | firstWall U z.1 z.2 < secondWall U z.1 z.2}

def firstCornerSource (U : Set Plane) : Set Plane :=
  firstSourceSlice ∩ {z | firstWall U z.1 z.2 = secondWall U z.1 z.2}

def secondTangentSource (U : Set Plane) : Set Plane :=
  secondSourceSlice ∩ {z |
    secondWall U (z.1 - Real.pi / 2) z.2 < firstWall U (z.1 - Real.pi / 2) z.2}

def secondCornerSource (U : Set Plane) : Set Plane :=
  secondSourceSlice ∩ {z |
    firstWall U (z.1 - Real.pi / 2) z.2 = secondWall U (z.1 - Real.pi / 2) z.2}

theorem measurable_joint_walls {U : Set Plane} (hU : IsCompact U) {f : Plane → ℝ}
    (hf : Measurable f) : Measurable (fun z : Plane => firstWall U (f z) z.2) ∧
      Measurable (fun z : Plane => secondWall U (f z) z.2) := by
  have := continuous_support hU
  have := continuous_unitNormal
  have := continuous_companionNormal
  unfold firstWall secondWall
  constructor <;> fun_prop

theorem measurableSet_firstTangentSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (firstTangentSource U) :=
  have h := measurable_joint_walls hU measurable_fst
  (measurableSet_Ioo.preimage measurable_fst).inter (measurableSet_lt h.1 h.2)

theorem measurableSet_firstCornerSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (firstCornerSource U) :=
  have h := measurable_joint_walls hU measurable_fst
  (measurableSet_Ioo.preimage measurable_fst).inter (measurableSet_eq_fun h.1 h.2)

theorem measurableSet_secondTangentSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (secondTangentSource U) :=
  have h := measurable_joint_walls hU (measurable_fst.sub_const (Real.pi / 2))
  (measurableSet_Ioo.preimage measurable_fst).inter (measurableSet_lt h.2 h.1)

theorem measurableSet_secondCornerSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (secondCornerSource U) :=
  have h := measurable_joint_walls hU (measurable_fst.sub_const (Real.pi / 2))
  (measurableSet_Ioo.preimage measurable_fst).inter (measurableSet_eq_fun h.1 h.2)

theorem disjoint_sourceSlices : Disjoint firstSourceSlice secondSourceSlice :=
  Set.disjoint_left.mpr fun _ hz ht => lt_asymm hz.2 ht.1

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def sourceBranchMeasure (S : Set Plane) : Measure Plane :=
  (J.measure : Measure Plane).restrict S

def sourceBranchAngular (S : Set Plane) (d : ℝ) : Measure ℝ :=
  (J.sourceBranchMeasure S).map (fun z => z.1 - d)

def sourceBranchDensity (S : Set Plane) (d t : ℝ) : ℝ :=
  realRnDensity (J.sourceBranchAngular S d) volume t

instance sourceBranchMeasure_isFinite (S : Set Plane) :
    IsFiniteMeasure (J.sourceBranchMeasure S) := by unfold sourceBranchMeasure; infer_instance

instance sourceBranchAngular_isFinite (S : Set Plane) (d : ℝ) :
    IsFiniteMeasure (J.sourceBranchAngular S d) := by unfold sourceBranchAngular; infer_instance

theorem sourceBranchMeasure_le (S : Set Plane) :
    J.sourceBranchMeasure S ≤ (J.measure : Measure Plane) := Measure.restrict_le_self

theorem measurable_sourceBranchDensity (S : Set Plane) (d : ℝ) :
    Measurable (J.sourceBranchDensity S d) :=
  measurable_realRnDensity _ _

theorem sourceBranchDensity_nonneg (S : Set Plane) (d t : ℝ) :
    0 ≤ J.sourceBranchDensity S d t := realRnDensity_nonneg _ _ _

theorem first_source_partition (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchMeasure (firstTangentSource target) +
      J.sourceBranchMeasure (firstCornerSource target) =
        J.sourceBranchMeasure firstSourceSlice := by
  unfold sourceBranchMeasure
  rw [← Measure.restrict_union (Set.disjoint_left.mpr fun _ hz ht => hz.2.ne ht.2)
    (measurableSet_firstCornerSource hTarget.isCompact)]
  refine Measure.restrict_congr_set ?_
  filter_upwards [J.ae_first_wall_contact hTarget, hpositive] with z hz hp
  refine propext ⟨fun h => h.elim And.left And.left, fun ht => ?_⟩
  have hle : firstWall target z.1 z.2 ≤ secondWall target z.1 z.2 := min_eq_left_iff.1
    ((positive_fullWallClip_eq_cornerWall (U := hTarget.toCompactCap) hp (hz ht).2).trans
      (hz ht).1.symm)
  exact hle.lt_or_eq.imp (⟨ht, ·⟩) (⟨ht, ·⟩)

theorem second_source_partition (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchMeasure (secondTangentSource target) +
      J.sourceBranchMeasure (secondCornerSource target) =
        J.sourceBranchMeasure secondSourceSlice := by
  unfold sourceBranchMeasure
  rw [← Measure.restrict_union (Set.disjoint_left.mpr fun _ hz ht => hz.2.ne ht.2.symm)
    (measurableSet_secondCornerSource hTarget.isCompact)]
  refine Measure.restrict_congr_set ?_
  filter_upwards [J.ae_second_wall_contact hTarget, hpositive] with z hz hp
  refine propext ⟨fun h => h.elim And.left And.left, fun ht => ?_⟩
  have hle : secondWall target (z.1 - Real.pi / 2) z.2 ≤
      firstWall target (z.1 - Real.pi / 2) z.2 := min_eq_right_iff.1
    ((positive_fullWallClip_eq_cornerWall (U := hTarget.toCompactCap) hp (hz ht).2).trans
      (hz ht).1.symm)
  exact hle.lt_or_eq.imp (⟨ht, ·⟩) (⟨ht, ·.symm⟩)

theorem source_four_branch_partition (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    (J.sourceBranchMeasure (firstTangentSource target) +
      J.sourceBranchMeasure (firstCornerSource target)) +
      (J.sourceBranchMeasure (secondTangentSource target) +
        J.sourceBranchMeasure (secondCornerSource target)) =
          (J.measure : Measure Plane) := by
  rw [J.first_source_partition hTarget hpositive, J.second_source_partition hTarget hpositive,
    sourceBranchMeasure, sourceBranchMeasure, ← Measure.restrict_union disjoint_sourceSlices
      (measurableSet_Ioo.preimage measurable_fst)]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2)] with z hz hn
  exact hn.lt_or_gt.imp (⟨hz.1, ·⟩) (⟨·, hz.2⟩)

theorem ae_first_corner_source_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target),
      z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
        (z.2, sweptNiche target (Real.pi / 2) z.2) = attachedCorner target z.1 := by
  filter_upwards [ae_restrict_mem (measurableSet_firstCornerSource hTarget.isCompact),
    ae_restrict_of_ae (J.ae_first_wall_contact hTarget)] with z hz hc
  exact ⟨hz.1, wall_tie_eq_attachedCorner hz.1 (hc hz.1).1 (hz.2.symm.trans (hc hz.1).1)⟩

theorem ae_second_corner_source_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondCornerSource target),
      z.1 - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
        (z.2, sweptNiche target (Real.pi / 2) z.2) =
          attachedCorner target (z.1 - Real.pi / 2) := by
  filter_upwards [ae_restrict_mem (measurableSet_secondCornerSource hTarget.isCompact),
    ae_restrict_of_ae (J.ae_second_wall_contact hTarget)] with z hz hc
  have ht : z.1 - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  exact ⟨ht, wall_tie_eq_attachedCorner ht (hz.2.trans (hc hz.1).1) (hc hz.1).1⟩

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c K : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem sourceBranchAngular_eq_density (S : Set Plane) (d : ℝ) :
    J.sourceBranchAngular S d = volume.withDensity
      (fun t => ENNReal.ofReal (J.sourceBranchDensity S d t)) :=
  (withDensity_realRnDensity _ _ ((Measure.absolutelyContinuous_of_le
    (Measure.map_mono (J.sourceBranchMeasure_le S) (measurable_fst.sub_const d))).trans
      (J.shifted_angle_absolutelyContinuous hTarget hheight haffine hTargetBox hleft hright
        heq d))).symm

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq in
theorem ae_first_tangent_source_contact :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target),
      z.1 ∈ regularCornerDomain m ∧
        (z.2, sweptNiche target (Real.pi / 2) z.2) = firstTangency target z.1 := by
  have hregular : ∀ᵐ z ∂(J.measure : Measure Plane),
      z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) → z.1 ∈ regularCornerDomain m := by
    simpa only [sub_zero] using J.ae_shifted_angle_regularCorner hTarget hheight haffine
      hTargetBox hleft hright heq 0
  filter_upwards [ae_restrict_mem (measurableSet_firstTangentSource hTarget.isCap.isCompact),
    ae_restrict_of_ae (J.ae_first_wall_contact hTarget.isCap), ae_restrict_of_ae hregular]
    with z hz hc hr
  exact ⟨hr hz.1, hTarget.isCap.first_strict_contact_eq_tangency hρ hρ0 hρK heq
    (hr hz.1) (hc hz.1).1 hz.2⟩

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq in
theorem ae_second_tangent_source_contact :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      z.1 - Real.pi / 2 ∈ regularCornerDomain m ∧
        (z.2, sweptNiche target (Real.pi / 2) z.2) =
          secondTangency target (z.1 - Real.pi / 2) := by
  filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource hTarget.isCap.isCompact),
    ae_restrict_of_ae (J.ae_second_wall_contact hTarget.isCap),
    ae_restrict_of_ae (J.ae_shifted_angle_regularCorner hTarget hheight haffine
      hTargetBox hleft hright heq (Real.pi / 2))] with z hz hc hr
  have ht := hr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  exact ⟨ht, hTarget.isCap.second_strict_contact_eq_tangency hρ hρ0 hρK heq ht (hc hz.1).1 hz.2⟩

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq in
theorem ae_second_tangent_source_density_le_one :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target), ρ z.1 ≤ 1 := by
  have hbound := ae_of_ae_map (measurable_fst.sub_const (Real.pi / 2)).aemeasurable
    ((J.shifted_angle_absolutelyContinuous hTarget hheight haffine hTargetBox hleft hright heq
      (Real.pi / 2)).ae_le ((ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mp
        (hTarget.isCap.ae_companion_density_le_one_at_strict_contact hρ hρ0 hρK heq)))
  filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource hTarget.isCap.isCompact),
    J.ae_second_tangent_source_contact hTarget hheight haffine hTargetBox hleft hright
      hρ hρ0 hρK heq,
    ae_restrict_of_ae (J.ae_second_wall_contact hTarget.isCap),
    ae_restrict_of_ae hbound] with z hz hr hc hb
  simpa only [sub_add_cancel] using hb hr.1 z.2 (hc hz.1).1 hz.2

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
