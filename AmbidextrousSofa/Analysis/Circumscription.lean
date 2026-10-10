import AmbidextrousSofa.Analysis.AxisVariation

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
      coordDot (x, 0) (normal i) ≤ support U (normal i) := by
  intro x hx i
  rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact coordDot_le_support hU.isCompact (hU.baseline_mem hp) (normal i)

theorem subset_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) : U ⊆ circumscription U normal := by
  intro p hp
  have hx : p.1 ∈ horizontalProjection U := ⟨p, hp, rfl⟩
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at hx
  exact (mem_upperPolygon_iff _ _ _ _ _).mpr
    ⟨hx, hU.inStrip hp, fun i => coordDot_le_support hU.isCompact hp (normal i)⟩

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
  apply le_antisymm
  · apply support_le_of_forall (hU.nonempty.mono hsub)
    intro p hp
    exact ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i
  · exact support_mono hsub hU.nonempty (isCompact_upperPolygon _ _ _ _) _

theorem finiteBarrier_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    finiteBarrier (circumscription U normal) normal corners terminal =
      finiteBarrier U normal corners terminal := by
  funext x
  rw [finiteBarrier_eq_eval normal _ (support_circumscription hU normal),
    finiteBarrier_eq_eval normal _ (fun _ => rfl)]

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
  have hleft : a ≤ horizontalLeft U := by
    obtain ⟨q, hq, hqx⟩ := horizontalLeft_mem hU.nonempty hU.isCompact
    simpa only [hqx] using (hbox hq).1.1
  have hright : horizontalRight U ≤ b := by
    obtain ⟨q, hq, hqx⟩ := horizontalRight_mem hU.nonempty hU.isCompact
    simpa only [hqx] using (hbox hq).1.2
  exact ⟨⟨hleft.trans hx.1, hx.2.trans hright⟩, hy⟩

/-- The recovery inequality is for the actual three spatial windows; it
does not replace the physical niche by an integral in angle. -/
theorem finiteSpatialScore_le_circumscription {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteSpatialScore U normal corners terminal ≤
      finiteSpatialScore (circumscription U normal) normal corners terminal := by
  have hV := isDownwardCap_circumscription hU normal hnormal
  have hprojection := horizontalProjection_circumscription hU normal
  have hleft : horizontalLeft (circumscription U normal) = horizontalLeft U :=
    congrArg sInf hprojection
  have hright : horizontalRight (circumscription U normal) = horizontalRight U :=
    congrArg sSup hprojection
  have hroof : ∀ x, capRoof U x ≤ capRoof (circumscription U normal) x :=
    hU.capRoof_mono hV (subset_circumscription hU normal)
  have hUI (a b : ℝ) : IntervalIntegrable (capRoof U) volume a b := by
    apply intervalIntegrable_iff'.mpr
    simpa only [uIcc] using hU.integrableOn_capRoof_Icc (min a b) (max a b)
  have hVI (a b : ℝ) : IntervalIntegrable (capRoof (circumscription U normal)) volume a b := by
    apply intervalIntegrable_iff'.mpr
    simpa only [uIcc] using hV.integrableOn_capRoof_Icc (min a b) (max a b)
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hfirst := intervalIntegral.integral_mono_on
    (show horizontalLeft U ≤ horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4
      by linarith) (hUI _ _) (hVI _ _) (fun x _ => hroof x)
  have hlast := intervalIntegral.integral_mono_on
    (show horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤ horizontalRight U
      by linarith) (hUI _ _) (hVI _ _) (fun x _ => hroof x)
  unfold finiteSpatialScore
  rw [hleft, hright, finiteBarrier_circumscription hU normal corners terminal]
  unfold intervalSpatialScore
  linarith

end FinitePolygon

end AmbidextrousSofa
