module

public import AmbidextrousSofa.Analysis.AxisVariation

@[expose] public section

/-!
# Actual finite support circumscription

Intersecting the sampled support halfplanes with the actual projection
box produces a larger downward cap. Every sampled support remains exact,
and the actual projection is unchanged. Consequently the sampled physical
barrier and any sampled support penalty remain unchanged while the charged
exterior roof can only increase. These are the recovery competitors for
finite selected spatial maximizers.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

def circumscription (U : Set Plane) (normal : ι → Plane) : Set Plane :=
  upperPolygon (horizontalLeft U) (horizontalRight U) normal (fun i => support U (normal i))

theorem circumscription_baseline {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) :
    ∀ x ∈ Icc (horizontalLeft U) (horizontalRight U), ∀ i,
      coordDot (x, 0) (normal i) ≤ support U (normal i) := fun x hx i => by
  obtain ⟨p, hp, rfl⟩ := (horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex).ge hx
  exact coordDot_le_support hU.isCompact (hU.baseline_mem hp) (normal i)

theorem subset_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) : U ⊆ circumscription U normal := fun p hp =>
  (mem_upperPolygon_iff _ _ _ _ _).mpr
    ⟨(horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex).le ⟨p, hp, rfl⟩,
      hU.inStrip hp, fun i => coordDot_le_support hU.isCompact hp (normal i)⟩

theorem isDownwardCap_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2) :
    IsDownwardCap (circumscription U normal) :=
  isDownwardCap_upperPolygon _ _ _ _
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
    hnormal (circumscription_baseline hU normal)

theorem horizontalProjection_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) :
    horizontalProjection (circumscription U normal) = horizontalProjection U := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact horizontalProjection_upperPolygon _ _ _ _ (circumscription_baseline hU normal)

theorem support_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (i : ι) :
    support (circumscription U normal) (normal i) = support U (normal i) := by
  have hsub := subset_circumscription hU normal
  exact le_antisymm (support_le_of_forall (hU.nonempty.mono hsub) fun p hp =>
    ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i)
    (support_mono hsub hU.nonempty (isCompact_upperPolygon _ _ _ _) _)

theorem sampledPenalty_circumscription [Fintype ι] {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (weight target : ι → ℝ) :
    sampledPenalty (circumscription U normal) normal weight target =
      sampledPenalty U normal weight target :=
  sampledPenalty_eq_heightPenalty normal weight target _ (support_circumscription hU normal)

/-- Circumscription stays in the same fixed artificial box because its
own actual projection is fixed and its height is bounded by the strip. -/
theorem circumscription_subset_box {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) {a b : ℝ} (hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    circumscription U normal ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
  intro p hp
  obtain ⟨hx, hy, _⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
  obtain ⟨q, hq, hqx⟩ := horizontalLeft_mem hU.nonempty hU.isCompact
  obtain ⟨r, hr, hrx⟩ := horizontalRight_mem hU.nonempty hU.isCompact
  exact ⟨⟨by linarith [(hbox hq).1.1, hx.1], by linarith [(hbox hr).1.2, hx.2]⟩, hy⟩

/-- The recovery inequality is for the actual three spatial windows; it
does not replace the physical niche by an integral in angle. -/
theorem finiteSpatialScore_le_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteSpatialScore U normal corners terminal ≤
      finiteSpatialScore (circumscription U normal) normal corners terminal := by
  have hV := isDownwardCap_circumscription hU normal hnormal
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hB : finiteBarrier (circumscription U normal) normal corners terminal =
      finiteBarrier U normal corners terminal := funext fun x => by
    rw [finiteBarrier_eq_eval normal _ (support_circumscription hU normal),
      finiteBarrier_eq_eval normal _ (fun _ => rfl)]
  simp only [finiteSpatialScore, intervalSpatialScore, horizontalLeft, horizontalRight,
    horizontalProjection_circumscription hU normal, hB] at hlr ⊢
  gcongr ?_ + ?_ - _ <;> exact intervalIntegral.integral_mono (by linarith)
    ((intervalIntegrable_iff').mpr (hU.integrableOn_capRoof_Icc _ _))
    ((intervalIntegrable_iff').mpr (hV.integrableOn_capRoof_Icc _ _))
    (hU.capRoof_mono hV (subset_circumscription hU normal))

end FinitePolygon

end AmbidextrousSofa
