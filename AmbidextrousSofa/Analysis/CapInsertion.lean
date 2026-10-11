module

public import AmbidextrousSofa.Analysis.CapOrder
public import AmbidextrousSofa.Geometry.HullCompact

@[expose] public section

/-!
# Inserting a point into an actual downward cap

Insertion means convexifying the union with one point and filling its
vertical fibers down to the baseline. Supports in upward directions are
the maximum of the old support and the inserted point's coordinate pairing.
An inserted abscissa in the old projection preserves the exact projection.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def insertedCap (U : Set Plane) (p : Plane) : Set Plane :=
  upperCap (actualHull (insert p U))

theorem support_insert {U : Set Plane} (hU : IsCompact U) (hne : U.Nonempty)
    (p v : Plane) : support (insert p U) v = max (support U v) (coordDot p v) :=
  le_antisymm (support_le_of_forall (insert_nonempty p U) (forall_mem_insert.2
    ⟨le_max_right _ _, fun _ hq => (coordDot_le_support hU hq v).trans (le_max_left _ _)⟩))
    (max_le (support_mono (subset_insert p U) hne (hU.insert p) v)
      (coordDot_le_support (hU.insert p) (mem_insert p U) v))

theorem IsDownwardCap.isDownwardCap_insertedCap {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ unitStrip) :
    IsDownwardCap (insertedCap U p) :=
  isDownwardCap_upperCap (actualHull_nonempty (insert_nonempty p U))
    (isCompact_actualHull (hU.isCompact.insert p)) (convex_actualHull _)
    (actualHull_subset_unitStrip (insert_subset hp hU.inStrip))

theorem IsDownwardCap.subset_insertedCap {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ unitStrip) :
    U ⊆ insertedCap U p :=
  ((subset_insert p U).trans (subset_actualHull _)).trans (subset_upperCap fun _ hq =>
    (actualHull_subset_unitStrip (insert_subset hp hU.inStrip) hq).1)

theorem inserted_point_mem {U : Set Plane} {p : Plane} (hp : p ∈ unitStrip) :
    p ∈ insertedCap U p :=
  ⟨hp.1, p.2, le_rfl, subset_actualHull (insert p U) (mem_insert p U)⟩

theorem IsDownwardCap.support_insertedCap {U : Set Plane}
    (hU : IsDownwardCap U) {p v : Plane} (hp : p ∈ unitStrip) (hv : 0 ≤ v.2) :
    support (insertedCap U p) v = max (support U v) (coordDot p v) := by
  rw [insertedCap, support_upperCap (isCompact_actualHull (hU.isCompact.insert p))
    (actualHull_nonempty (insert_nonempty p U))
    (fun q hq => (actualHull_subset_unitStrip (insert_subset hp hU.inStrip) hq).1) hv,
    support_actualHull (hU.isCompact.insert p) (insert_nonempty p U),
    support_insert hU.isCompact hU.nonempty]

theorem IsDownwardCap.support_insertedCap_eq_of_dominated {U : Set Plane}
    (hU : IsDownwardCap U) {p v : Plane} (hp : p ∈ unitStrip) (hv : 0 ≤ v.2)
    (hdom : coordDot p v ≤ support U v) :
    support (insertedCap U p) v = support U v := by
  rw [hU.support_insertedCap hp hv, max_eq_left hdom]

theorem IsDownwardCap.horizontalLeft_insertedCap {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ unitStrip)
    (hpx : p.1 ∈ horizontalProjection U) :
    horizontalLeft (insertedCap U p) = horizontalLeft U := by
  have hV := hU.isDownwardCap_insertedCap hp
  obtain ⟨q, hq, hqx⟩ := hpx
  have heq := hU.support_insertedCap_eq_of_dominated (v := (-1, 0)) hp (by norm_num) (by
    simpa only [coordDot, mul_neg_one, mul_zero, add_zero, hqx] using
      coordDot_le_support hU.isCompact hq (-1, 0))
  rwa [support_horizontal_left hV.isCompact hV.nonempty,
    support_horizontal_left hU.isCompact hU.nonempty, neg_inj] at heq

theorem IsDownwardCap.horizontalRight_insertedCap {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ unitStrip)
    (hpx : p.1 ∈ horizontalProjection U) :
    horizontalRight (insertedCap U p) = horizontalRight U := by
  obtain ⟨q, hq, hqx⟩ := hpx
  simpa only [support_horizontal_right] using
    hU.support_insertedCap_eq_of_dominated (v := (1, 0)) hp (by norm_num) (by
      simpa only [coordDot, mul_one, mul_zero, add_zero, hqx] using
        coordDot_le_support hU.isCompact hq (1, 0))

theorem IsDownwardCap.horizontalProjection_insertedCap {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ unitStrip)
    (hpx : p.1 ∈ horizontalProjection U) :
    horizontalProjection (insertedCap U p) = horizontalProjection U := by
  have hV := hU.isDownwardCap_insertedCap hp
  rw [horizontalProjection_eq_Icc hV.nonempty hV.isCompact hV.convex,
    horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex,
    hU.horizontalLeft_insertedCap hp hpx, hU.horizontalRight_insertedCap hp hpx]

theorem IsDownwardCap.capRoof_inserted_one {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) : capRoof (insertedCap U (x, 1)) x = 1 := by
  have hp : (x, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  have hV := hU.isDownwardCap_insertedCap hp
  exact le_antisymm (capRoof_le_one hV.isCompact hV.inStrip x)
    (le_capRoof hV.isCompact (inserted_point_mem hp))

end AmbidextrousSofa
