module

public import AmbidextrousSofa.Analysis.FiniteScore
public import AmbidextrousSofa.Analysis.DyadicGrid

@[expose] public section

/-!
# Actual polygon source indices for a quarter-angle grid

Only open-quarter samples produce moving upper walls. The two endpoints
have zero clipped height and are represented by the baseline leaf. Each
interior angle contributes its actual first and companion normal, and the
literal finite barrier equals the finite angular niche. The resulting
spatial slopes are distinct, with no repeated-source approximation.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

def interior (grid : Finset QuarterAngle) : Finset QuarterAngle := by
  classical
  exact grid.filter (fun t => 0 < (t : ℝ) ∧ (t : ℝ) < Real.pi / 2)

abbrev InteriorPoint (grid : Finset QuarterAngle) := ↥(interior grid)

abbrev SourceIndex (grid : Finset QuarterAngle) := InteriorPoint grid ⊕ InteriorPoint grid

theorem interiorPoint_mem (grid : Finset QuarterAngle) (t : InteriorPoint grid) :
    0 < (t.val : ℝ) ∧ (t.val : ℝ) < Real.pi / 2 :=
  (Finset.mem_filter.mp t.property).2

theorem interiorPoint_mem_grid (grid : Finset QuarterAngle) (t : InteriorPoint grid) :
    t.val ∈ grid :=
  (Finset.mem_filter.mp t.property).1

def normal (grid : Finset QuarterAngle) : SourceIndex grid → Plane
  | Sum.inl t => unitNormal t.val
  | Sum.inr t => companionNormal t.val

def fullAngle (grid : Finset QuarterAngle) : SourceIndex grid → ℝ
  | Sum.inl t => t.val
  | Sum.inr t => (t.val : ℝ) + Real.pi / 2

def pairList (grid : Finset QuarterAngle) : List (SourceIndex grid × SourceIndex grid) := by
  classical
  exact (Finset.univ : Finset (InteriorPoint grid)).toList.map
    (fun t => (Sum.inl t, Sum.inr t))

theorem pair_mem_pairList (grid : Finset QuarterAngle) (t : InteriorPoint grid) :
    (Sum.inl t, Sum.inr t) ∈ pairList grid :=
  List.mem_map.mpr ⟨t, by simp, rfl⟩

theorem normal_eq_unitNormal (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    normal grid i = unitNormal (fullAngle grid i) := by
  rcases i with t | t
  exacts [rfl, companionNormal_eq_unitNormal _]

theorem fullAngle_mem (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    fullAngle grid i ∈ Ioo (0 : ℝ) Real.pi := by
  rcases i with t | t <;> have := interiorPoint_mem grid t <;>
    constructor <;> simp only [fullAngle] <;> linarith

theorem fullAngle_injective (grid : Finset QuarterAngle) : Function.Injective (fullAngle grid) := by
  rintro (s | s) (t | t) h <;> have := interiorPoint_mem grid s <;>
    have := interiorPoint_mem grid t <;>
    simp only [fullAngle, Sum.inl.injEq, Sum.inr.injEq, Subtype.ext_iff, reduceCtorEq] at h ⊢ <;>
    linarith

theorem normal_snd_pos (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    0 < (normal grid i).2 := by
  rw [normal_eq_unitNormal]
  exact Real.sin_pos_of_pos_of_lt_pi (fullAngle_mem grid i).1 (fullAngle_mem grid i).2

theorem normal_fst_ne_zero (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    (normal grid i).1 ≠ 0 := by
  rcases i with t | t <;> obtain ⟨h0, h1⟩ := interiorPoint_mem grid t
  · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩).ne'
  · exact neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)).ne'

theorem normal_unit (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    coordDot (normal grid i) (normal grid i) = 1 := by
  simp [normal_eq_unitNormal, coordDot, unitNormal, ← sq]

theorem normal_det_ne_zero (grid : Finset QuarterAngle) {i j : SourceIndex grid} (hij : i ≠ j) :
    (normal grid i).1 * (normal grid j).2 -
      (normal grid i).2 * (normal grid j).1 ≠ 0 := by
  obtain ⟨hi0, hi1⟩ := fullAngle_mem grid i
  obtain ⟨hj0, hj1⟩ := fullAngle_mem grid j
  rw [show _ - _ = Real.sin (fullAngle grid j - fullAngle grid i) by
      simp only [normal_eq_unitNormal, unitNormal, Real.sin_sub]; ring,
    Ne, Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith), sub_eq_zero]
  exact (fullAngle_injective grid).ne hij.symm

theorem wallSlopes_injective (grid : Finset QuarterAngle) :
    Function.Injective (wallSlope (normal grid)) :=
  wallSlope_injective (normal grid) (normal_snd_pos grid) (normal_fst_ne_zero grid)
    (fun _ _ hij => normal_det_ne_zero grid hij)

/-- The physical first/companion polygon sources give exactly the angular
maximum used in the uniform approximation theorem. -/
theorem finiteBarrier_eq_niche {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (x : ℝ) :
    finiteBarrier U (normal grid) (pairList grid) none x = niche hU.toCompactCap grid x := by
  show finiteNiche U (normal grid) (pairList grid) x = _
  have h0 := finiteNiche_nonneg U (normal grid) (pairList grid) x
  refine le_antisymm ((finiteNiche_le_iff ..).mpr ⟨niche_nonneg .., ?_⟩)
    ((niche_le_iff ..).mpr ⟨h0, fun t ht => ?_⟩)
  · simp only [pairList, List.mem_map]
    rintro _ ⟨t, _, rfl⟩
    rw [normal, normal, supportWall_unitNormal, supportWall_companionNormal]
    exact (le_max_left _ _).trans
      (clip_le_niche hU.toCompactCap grid x (interiorPoint_mem_grid grid t))
  rcases t.2.1.eq_or_lt with ht0 | ht0
  · rwa [← ht0, fullWallClip_zero]
  rcases t.2.2.eq_or_lt with htL | htL
  · rwa [htL, fullWallClip_pi_div_two]
  have h := ((finiteNiche_le_iff U (normal grid) _ x _).mp le_rfl).2 _
    (pair_mem_pairList grid ⟨t, Finset.mem_filter.mpr ⟨ht, ht0, htL⟩⟩)
  rw [normal, normal, supportWall_unitNormal, supportWall_companionNormal] at h
  exact max_le h h0

end AngularGrid

end AmbidextrousSofa
