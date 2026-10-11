module

public import AmbidextrousSofa.Analysis.JointSourcePositive
public import AmbidextrousSofa.Analysis.PositiveWallContacts

@[expose] public section

/-!
# The four literal branches of the common source measure

Strict wall slack tags a tangent source; equality of the two walls tags
a corner source. The four measures below are restrictions of the same
selected joint measure. Their partition is proved from its actual
positive wall contacts. No separate choice of a first or companion
occupation measure is made. When the angular marginal is absolutely
continuous, every translated branch marginal has a Radon--Nikodym
density, and the tangent branches lie on the actual tangency loci.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def firstSourceSlice : Set Plane := Prod.fst ⁻¹' Ioo (0 : ℝ) (Real.pi / 2)

def secondSourceSlice : Set Plane := Prod.fst ⁻¹' Ioo (Real.pi / 2) Real.pi

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

/-- A slice almost all of whose points lie in one of two disjoint parts is their union. -/
theorem restrict_add_restrict_eq_of_ae {μ : Measure Plane} {S A B : Set Plane}
    (hB : MeasurableSet B) (hA : A ⊆ S) (hBS : B ⊆ S) (hAB : Disjoint A B)
    (h : ∀ᵐ z ∂μ, z ∈ S → z ∈ A ∨ z ∈ B) : μ.restrict A + μ.restrict B = μ.restrict S := by
  rw [← Measure.restrict_union hAB hB]
  refine Measure.restrict_congr_set ?_
  filter_upwards [h] with z hz
  exact propext ⟨fun h => h.elim (hA ·) (hBS ·), hz⟩

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b)

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

/-- With an absolutely continuous angular marginal, every translated branch marginal has its
Radon--Nikodym density. -/
theorem sourceBranchAngular_eq_density (hac : J.angularMeasure ≪ volume) (S : Set Plane)
    (d : ℝ) : J.sourceBranchAngular S d = volume.withDensity
      (fun t => ENNReal.ofReal (J.sourceBranchDensity S d t)) :=
  (withDensity_realRnDensity _ _ ((Measure.absolutelyContinuous_of_le
    (Measure.map_mono (J.sourceBranchMeasure_le S) (measurable_fst.sub_const d))).trans
      (J.shifted_angle_absolutelyContinuous hac d))).symm

section ActualDensity

variable (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)
include H

theorem first_source_partition :
    J.sourceBranchMeasure (firstTangentSource target) +
      J.sourceBranchMeasure (firstCornerSource target) =
        J.sourceBranchMeasure firstSourceSlice := by
  refine restrict_add_restrict_eq_of_ae (measurableSet_firstCornerSource H.hU.isCap.isCompact)
    inter_subset_left inter_subset_left (Set.disjoint_left.mpr fun _ hz ht => hz.2.ne ht.2) ?_
  filter_upwards [J.ae_first_wall_contact H.hU.isCap, J.ae_niche_pos H] with z hz hp ht
  exact (min_eq_left_iff.1 ((positive_fullWallClip_eq_cornerWall (U := H.hU.isCap.toCompactCap)
    hp (hz ht).2).trans (hz ht).1.symm)).lt_or_eq.imp (⟨ht, ·⟩) (⟨ht, ·⟩)

theorem second_source_partition :
    J.sourceBranchMeasure (secondTangentSource target) +
      J.sourceBranchMeasure (secondCornerSource target) =
        J.sourceBranchMeasure secondSourceSlice := by
  refine restrict_add_restrict_eq_of_ae (measurableSet_secondCornerSource H.hU.isCap.isCompact)
    inter_subset_left inter_subset_left (Set.disjoint_left.mpr fun _ hz ht => hz.2.ne ht.2.symm) ?_
  filter_upwards [J.ae_second_wall_contact H.hU.isCap, J.ae_niche_pos H] with z hz hp ht
  exact (min_eq_right_iff.1 ((positive_fullWallClip_eq_cornerWall (U := H.hU.isCap.toCompactCap)
    hp (hz ht).2).trans (hz ht).1.symm)).lt_or_eq.imp (⟨ht, ·⟩) (⟨ht, ·.symm⟩)

theorem source_four_branch_partition :
    (J.sourceBranchMeasure (firstTangentSource target) +
      J.sourceBranchMeasure (firstCornerSource target)) +
      (J.sourceBranchMeasure (secondTangentSource target) +
        J.sourceBranchMeasure (secondCornerSource target)) =
          (J.measure : Measure Plane) := by
  rw [J.first_source_partition H, J.second_source_partition H, sourceBranchMeasure,
    sourceBranchMeasure, ← Measure.restrict_union disjoint_sourceSlices
      (measurableSet_Ioo.preimage measurable_fst)]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2)] with z hz hn
  exact hn.lt_or_gt.imp (⟨hz.1, ·⟩) (⟨·, hz.2⟩)

theorem ae_first_tangent_source_graph :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target),
      z.2 = (firstTangency target z.1).1 := by
  filter_upwards [ae_restrict_mem (measurableSet_firstTangentSource H.hU.isCap.isCompact),
    ae_restrict_of_ae (J.ae_first_wall_contact H.hU.isCap), ae_restrict_of_ae
      (J.ae_shifted_angle_regularCorner (m := m) (J.angularMeasure_absolutelyContinuous H) 0)]
    with z hz hc hr
  have ht : z.1 ∈ regularCornerDomain m := by
    simpa only [sub_zero] using hr (by rw [sub_zero]; exact hz.1)
  exact congrArg Prod.fst (H.hU.isCap.first_strict_contact_eq_tangency H.hρ H.hρ0 H.hρK H.heq ht
    (hc hz.1).1 hz.2)

theorem ae_second_tangent_source_contact :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      z.1 - Real.pi / 2 ∈ regularCornerDomain m ∧
        (z.2, sweptNiche target (Real.pi / 2) z.2) =
          secondTangency target (z.1 - Real.pi / 2) := by
  filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource H.hU.isCap.isCompact),
    ae_restrict_of_ae (J.ae_second_wall_contact H.hU.isCap), ae_restrict_of_ae
      (J.ae_shifted_angle_regularCorner (J.angularMeasure_absolutelyContinuous H) (Real.pi / 2))]
    with z hz hc hr
  have ht := hr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  exact ⟨ht, H.hU.isCap.second_strict_contact_eq_tangency H.hρ H.hρ0 H.hρK H.heq ht (hc hz.1).1
    hz.2⟩

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
