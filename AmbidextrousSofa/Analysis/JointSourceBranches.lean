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

theorem measurableSet_firstSourceSlice : MeasurableSet firstSourceSlice :=
  measurableSet_Ioo.preimage measurable_fst

theorem measurableSet_secondSourceSlice : MeasurableSet secondSourceSlice :=
  measurableSet_Ioo.preimage measurable_fst

theorem measurable_joint_firstWall {U : Set Plane} (hU : IsCompact U) :
    Measurable (fun z : Plane => firstWall U z.1 z.2) := by
  have hs := ((continuous_support hU).comp
    (continuous_unitNormal.comp (continuous_fst : Continuous (fun z : Plane => z.1)))).measurable
  exact ((hs.sub measurable_const).sub
    (measurable_snd.mul (Real.measurable_cos.comp measurable_fst))).div
    (Real.measurable_sin.comp measurable_fst)

theorem measurable_joint_secondWall {U : Set Plane} (hU : IsCompact U) :
    Measurable (fun z : Plane => secondWall U z.1 z.2) := by
  have hs := ((continuous_support hU).comp
    (continuous_companionNormal.comp (continuous_fst : Continuous (fun z : Plane => z.1)))).measurable
  exact ((hs.sub measurable_const).add
    (measurable_snd.mul (Real.measurable_sin.comp measurable_fst))).div
    (Real.measurable_cos.comp measurable_fst)

theorem measurableSet_firstTangentSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (firstTangentSource U) :=
  measurableSet_firstSourceSlice.inter
    (measurableSet_lt (measurable_joint_firstWall hU) (measurable_joint_secondWall hU))

theorem measurableSet_firstCornerSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (firstCornerSource U) :=
  measurableSet_firstSourceSlice.inter
    (measurableSet_eq_fun (measurable_joint_firstWall hU) (measurable_joint_secondWall hU))

theorem measurableSet_secondTangentSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (secondTangentSource U) := by
  have hm : Measurable (fun z : Plane => (z.1 - Real.pi / 2, z.2)) :=
    (measurable_fst.sub_const _).prodMk measurable_snd
  have h1 := (measurable_joint_secondWall hU).comp hm
  have h2 := (measurable_joint_firstWall hU).comp hm
  exact measurableSet_secondSourceSlice.inter (measurableSet_lt h1 h2)

theorem measurableSet_secondCornerSource {U : Set Plane} (hU : IsCompact U) :
    MeasurableSet (secondCornerSource U) := by
  have hm : Measurable (fun z : Plane => (z.1 - Real.pi / 2, z.2)) :=
    (measurable_fst.sub_const _).prodMk measurable_snd
  have h1 := (measurable_joint_firstWall hU).comp hm
  have h2 := (measurable_joint_secondWall hU).comp hm
  exact measurableSet_secondSourceSlice.inter (measurableSet_eq_fun h1 h2)

theorem disjoint_firstSource_branches (U : Set Plane) :
    Disjoint (firstTangentSource U) (firstCornerSource U) := by
  apply Set.disjoint_left.mpr
  intro z hz ht
  exact hz.2.ne ht.2

theorem disjoint_secondSource_branches (U : Set Plane) :
    Disjoint (secondTangentSource U) (secondCornerSource U) := by
  apply Set.disjoint_left.mpr
  intro z hz ht
  exact hz.2.ne ht.2.symm

theorem disjoint_sourceSlices : Disjoint firstSourceSlice secondSourceSlice := by
  apply Set.disjoint_left.mpr
  intro z hz ht
  exact (not_lt_of_ge hz.2.le) ht.1

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def sourceBranchMeasure (S : Set Plane) : Measure Plane :=
  (J.measure : Measure Plane).restrict S

def sourceBranchAngular (S : Set Plane) (d : ℝ) : Measure ℝ :=
  (J.sourceBranchMeasure S).map (fun z => z.1 - d)

def sourceBranchDensity (S : Set Plane) (d t : ℝ) : ℝ :=
  realRnDensity (J.sourceBranchAngular S d) volume t

instance sourceBranchMeasure_isFinite (S : Set Plane) :
    IsFiniteMeasure (J.sourceBranchMeasure S) := by
  unfold sourceBranchMeasure
  infer_instance

instance sourceBranchAngular_isFinite (S : Set Plane) (d : ℝ) :
    IsFiniteMeasure (J.sourceBranchAngular S d) := by
  unfold sourceBranchAngular
  infer_instance

theorem sourceBranchMeasure_le (S : Set Plane) :
    J.sourceBranchMeasure S ≤ (J.measure : Measure Plane) := Measure.restrict_le_self

theorem sourceBranchAngular_le (S : Set Plane) (d : ℝ) :
    J.sourceBranchAngular S d ≤ (J.measure : Measure Plane).map (fun z => z.1 - d) :=
  Measure.map_mono (J.sourceBranchMeasure_le S) (measurable_fst.sub_const d)

theorem measurable_sourceBranchDensity (S : Set Plane) (d : ℝ) :
    Measurable (J.sourceBranchDensity S d) :=
  measurable_realRnDensity _ _

theorem sourceBranchDensity_nonneg (S : Set Plane) (d t : ℝ) :
    0 ≤ J.sourceBranchDensity S d t := realRnDensity_nonneg _ _ _

theorem integrable_sourceBranchDensity (S : Set Plane) (d : ℝ) :
    Integrable (J.sourceBranchDensity S d) volume :=
  integrable_realRnDensity _ _

theorem first_source_partition (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchMeasure (firstTangentSource target) +
      J.sourceBranchMeasure (firstCornerSource target) =
        J.sourceBranchMeasure firstSourceSlice := by
  change (J.measure : Measure Plane).restrict (firstTangentSource target) +
    (J.measure : Measure Plane).restrict (firstCornerSource target) = _
  rw [← Measure.restrict_union (disjoint_firstSource_branches target)
    (measurableSet_firstCornerSource hTarget.isCompact)]
  apply Measure.restrict_congr_set
  filter_upwards [J.ae_first_wall_contact hTarget, hpositive] with z hz hp
  apply propext
  constructor
  · rintro (ht | hc)
    · exact ht.1
    · exact hc.1
  · intro ht
    have hh := hz ht
    have hm : cornerWall target z.1 z.2 = sweptNiche target (Real.pi / 2) z.2 :=
      positive_fullWallClip_eq_cornerWall (U := hTarget.toCompactCap) hp hh.2
    have hle : firstWall target z.1 z.2 ≤ secondWall target z.1 z.2 := by
      rw [hh.1, ← hm]
      exact min_le_right _ _
    rcases hle.lt_or_eq with hs | he
    · exact Or.inl ⟨ht, hs⟩
    · exact Or.inr ⟨ht, he⟩

theorem second_source_partition (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchMeasure (secondTangentSource target) +
      J.sourceBranchMeasure (secondCornerSource target) =
        J.sourceBranchMeasure secondSourceSlice := by
  change (J.measure : Measure Plane).restrict (secondTangentSource target) +
    (J.measure : Measure Plane).restrict (secondCornerSource target) = _
  rw [← Measure.restrict_union (disjoint_secondSource_branches target)
    (measurableSet_secondCornerSource hTarget.isCompact)]
  apply Measure.restrict_congr_set
  filter_upwards [J.ae_second_wall_contact hTarget, hpositive] with z hz hp
  apply propext
  constructor
  · rintro (ht | hc)
    · exact ht.1
    · exact hc.1
  · intro ht
    have hh := hz ht
    have hm : cornerWall target (z.1 - Real.pi / 2) z.2 = sweptNiche target (Real.pi / 2) z.2 :=
      positive_fullWallClip_eq_cornerWall (U := hTarget.toCompactCap) hp hh.2
    have hle : secondWall target (z.1 - Real.pi / 2) z.2 ≤
        firstWall target (z.1 - Real.pi / 2) z.2 := by
      rw [hh.1, ← hm]
      exact min_le_left _ _
    rcases hle.lt_or_eq with hs | he
    · exact Or.inl ⟨ht, hs⟩
    · exact Or.inr ⟨ht, he.symm⟩

theorem source_slices_partition :
    J.sourceBranchMeasure firstSourceSlice + J.sourceBranchMeasure secondSourceSlice =
      (J.measure : Measure Plane) := by
  change (J.measure : Measure Plane).restrict firstSourceSlice +
    (J.measure : Measure Plane).restrict secondSourceSlice = _
  rw [← Measure.restrict_union disjoint_sourceSlices measurableSet_secondSourceSlice]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2)] with z hz hn
  rcases lt_or_gt_of_ne hn with ht | ht
  · exact Or.inl ⟨hz.1, ht⟩
  · exact Or.inr ⟨ht, hz.2⟩

theorem source_four_branch_partition (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    (J.sourceBranchMeasure (firstTangentSource target) +
      J.sourceBranchMeasure (firstCornerSource target)) +
      (J.sourceBranchMeasure (secondTangentSource target) +
        J.sourceBranchMeasure (secondCornerSource target)) =
          (J.measure : Measure Plane) := by
  rw [J.first_source_partition hTarget hpositive,
    J.second_source_partition hTarget hpositive, J.source_slices_partition]

theorem ae_first_corner_source_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target),
      z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
        (z.2, sweptNiche target (Real.pi / 2) z.2) = attachedCorner target z.1 := by
  filter_upwards [ae_restrict_mem (measurableSet_firstCornerSource hTarget.isCompact),
    ae_restrict_of_ae (J.ae_first_wall_contact hTarget)] with z hz hc
  exact ⟨hz.1, wall_tie_eq_attachedCorner hz.1 (hc hz.1).1
    (hz.2.symm.trans (hc hz.1).1)⟩

theorem ae_second_corner_source_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondCornerSource target),
      z.1 - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
        (z.2, sweptNiche target (Real.pi / 2) z.2) =
          attachedCorner target (z.1 - Real.pi / 2) := by
  filter_upwards [ae_restrict_mem (measurableSet_secondCornerSource hTarget.isCompact),
    ae_restrict_of_ae (J.ae_second_wall_contact hTarget)] with z hz hc
  have ht : z.1 - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith only [hz.1.1, hz.1.2]
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
theorem sourceBranchAngular_absolutelyContinuous (S : Set Plane) (d : ℝ) :
    J.sourceBranchAngular S d ≪ (volume : Measure ℝ) :=
  (Measure.absolutelyContinuous_of_le (J.sourceBranchAngular_le S d)).trans
    (J.shifted_angle_absolutelyContinuous hTarget hheight haffine hTargetBox hleft hright heq d)

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem sourceBranchAngular_eq_density (S : Set Plane) (d : ℝ) :
    J.sourceBranchAngular S d = volume.withDensity
      (fun t => ENNReal.ofReal (J.sourceBranchDensity S d t)) :=
  (withDensity_realRnDensity _ _ (J.sourceBranchAngular_absolutelyContinuous hTarget
    hheight haffine hTargetBox hleft hright heq S d)).symm

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
  have ht : z.1 - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith only [hz.1.1, hz.1.2]
  exact ⟨hr ht, hTarget.isCap.second_strict_contact_eq_tangency hρ hρ0 hρK heq
    (hr ht) (hc hz.1).1 hz.2⟩

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq in
theorem ae_second_tangent_source_density_le_one :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target), ρ z.1 ≤ 1 := by
  have hbound : ∀ᵐ t : ℝ ∂volume,
      t ∈ regularCornerDomain m → ∀ x : ℝ,
        secondWall target t x = sweptNiche target (Real.pi / 2) x →
        secondWall target t x < firstWall target t x → ρ (t + Real.pi / 2) ≤ 1 :=
    (ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mp
      (hTarget.isCap.ae_companion_density_le_one_at_strict_contact hρ hρ0 hρK heq)
  have hboundJ := (J.shifted_angle_absolutelyContinuous hTarget hheight haffine hTargetBox
    hleft hright heq (Real.pi / 2)).ae_le hbound
  have hboundM := ae_of_ae_map (measurable_fst.sub_const (Real.pi / 2)).aemeasurable hboundJ
  filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource hTarget.isCap.isCompact),
    J.ae_second_tangent_source_contact hTarget hheight haffine hTargetBox hleft hright
      hρ hρ0 hρK heq,
    ae_restrict_of_ae (J.ae_second_wall_contact hTarget.isCap),
    ae_restrict_of_ae hboundM] with z hz hr hc hb
  simpa only [sub_add_cancel] using hb hr.1 z.2 (hc hz.1).1 hz.2

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
