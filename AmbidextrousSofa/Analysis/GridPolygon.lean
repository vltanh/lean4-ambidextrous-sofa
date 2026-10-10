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
    0 < (t.val : ℝ) ∧ (t.val : ℝ) < Real.pi / 2 := by
  classical
  exact (Finset.mem_filter.mp t.property).2

theorem interiorPoint_mem_grid (grid : Finset QuarterAngle) (t : InteriorPoint grid) :
    t.val ∈ grid := by
  classical
  exact (Finset.mem_filter.mp t.property).1

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
    (Sum.inl t, Sum.inr t) ∈ pairList grid := by
  classical
  apply List.mem_map.mpr
  exact ⟨t, by simp, rfl⟩

theorem normal_eq_unitNormal (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    normal grid i = unitNormal (fullAngle grid i) := by
  cases i with
  | inl t => rfl
  | inr t => exact companionNormal_eq_unitNormal _

theorem fullAngle_mem (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    fullAngle grid i ∈ Ioo (0 : ℝ) Real.pi := by
  cases i with
  | inl t =>
    have ht := interiorPoint_mem grid t
    change 0 < (t.val : ℝ) ∧ (t.val : ℝ) < Real.pi
    constructor <;> linarith [Real.pi_pos]
  | inr t =>
    have ht := interiorPoint_mem grid t
    change 0 < (t.val : ℝ) + Real.pi / 2 ∧ (t.val : ℝ) + Real.pi / 2 < Real.pi
    constructor <;> linarith [Real.pi_pos]

theorem fullAngle_injective (grid : Finset QuarterAngle) : Function.Injective (fullAngle grid) := by
  intro i j heq
  cases i with
  | inl s =>
    cases j with
    | inl t =>
      congr 1
      exact Subtype.ext (Subtype.ext heq)
    | inr t =>
      have hs := interiorPoint_mem grid s
      have ht := interiorPoint_mem grid t
      change (s.val : ℝ) = (t.val : ℝ) + Real.pi / 2 at heq
      exfalso
      linarith
  | inr s =>
    cases j with
    | inl t =>
      have hs := interiorPoint_mem grid s
      have ht := interiorPoint_mem grid t
      change (s.val : ℝ) + Real.pi / 2 = (t.val : ℝ) at heq
      exfalso
      linarith
    | inr t =>
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      change (s.val : ℝ) + Real.pi / 2 = (t.val : ℝ) + Real.pi / 2 at heq
      linarith

theorem normal_snd_pos (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    0 < (normal grid i).2 := by
  rw [normal_eq_unitNormal]
  exact Real.sin_pos_of_pos_of_lt_pi (fullAngle_mem grid i).1 (fullAngle_mem grid i).2

theorem normal_fst_ne_zero (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    (normal grid i).1 ≠ 0 := by
  cases i with
  | inl t =>
    have ht := interiorPoint_mem grid t
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht.2⟩).ne'
  | inr t =>
    have ht := interiorPoint_mem grid t
    exact neg_ne_zero.mpr
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])).ne'

theorem normal_unit (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    coordDot (normal grid i) (normal grid i) = 1 := by
  simp only [normal_eq_unitNormal, coordDot, unitNormal]
  nlinarith [Real.sin_sq_add_cos_sq (fullAngle grid i)]

theorem sourceSlope_eq_tan (grid : Finset QuarterAngle) (i : SourceIndex grid) :
    wallSlope (normal grid) (some i) = Real.tan (fullAngle grid i - Real.pi / 2) := by
  change -(normal grid i).1 / (normal grid i).2 = _
  simp only [normal_eq_unitNormal]
  simp [unitNormal, Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub]

theorem sourceSlope_injective (grid : Finset QuarterAngle) :
    Function.Injective (fun i : SourceIndex grid => wallSlope (normal grid) (some i)) := by
  intro i j heq
  dsimp only at heq
  rw [sourceSlope_eq_tan, sourceSlope_eq_tan] at heq
  have hi := fullAngle_mem grid i
  have hj := fullAngle_mem grid j
  have hangles := Real.injOn_tan
    (show fullAngle grid i - Real.pi / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [hi.1, hi.2])
    (show fullAngle grid j - Real.pi / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [hj.1, hj.2]) heq
  exact fullAngle_injective grid (by linarith)

theorem normal_det_ne_zero (grid : Finset QuarterAngle) {i j : SourceIndex grid} (hij : i ≠ j) :
    (normal grid i).1 * (normal grid j).2 -
      (normal grid i).2 * (normal grid j).1 ≠ 0 := by
  intro hdet
  apply hij
  apply sourceSlope_injective grid
  change -(normal grid i).1 / (normal grid i).2 = -(normal grid j).1 / (normal grid j).2
  apply (div_eq_div_iff (normal_snd_pos grid i).ne' (normal_snd_pos grid j).ne').mpr
  nlinarith

theorem wallSlopes_injective (grid : Finset QuarterAngle) :
    Function.Injective (wallSlope (normal grid)) :=
  wallSlope_injective (normal grid) (normal_snd_pos grid) (normal_fst_ne_zero grid)
    (fun _ _ hij => normal_det_ne_zero grid hij)

/-- The physical first/companion polygon sources give exactly the angular
maximum used in the uniform approximation theorem. -/
theorem finiteBarrier_eq_niche {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (x : ℝ) :
    finiteBarrier U (normal grid) (pairList grid) none x = niche hU.toCompactCap grid x := by
  classical
  change finiteNiche U (normal grid) (pairList grid) x = niche hU.toCompactCap grid x
  apply le_antisymm
  · apply (finiteNiche_le_iff U (normal grid) (pairList grid) x _).mpr
    refine ⟨niche_nonneg _ _ _, ?_⟩
    intro ij hij
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hij
    have hclip := clip_le_niche hU.toCompactCap grid x (interiorPoint_mem_grid grid t)
    change min (supportWall U (unitNormal t.val) x)
      (supportWall U (companionNormal t.val) x) ≤ _
    rw [supportWall_unitNormal, supportWall_companionNormal]
    exact (le_max_left _ _).trans hclip
  · apply (niche_le_iff hU.toCompactCap grid x _).mpr
    refine ⟨finiteNiche_nonneg _ _ _ _, ?_⟩
    intro t ht
    by_cases ht0 : (t : ℝ) = 0
    · rw [ht0, fullWallClip_zero]
      exact finiteNiche_nonneg _ _ _ _
    by_cases htL : (t : ℝ) = Real.pi / 2
    · rw [htL, fullWallClip_pi_div_two]
      exact finiteNiche_nonneg _ _ _ _
    · have htopen : 0 < (t : ℝ) ∧ (t : ℝ) < Real.pi / 2 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 htL⟩
      let s : InteriorPoint grid := ⟨t, Finset.mem_filter.mpr ⟨ht, htopen⟩⟩
      have hsource := ((finiteNiche_le_iff U (normal grid) (pairList grid) x
        (finiteNiche U (normal grid) (pairList grid) x)).mp le_rfl).2
          (Sum.inl s, Sum.inr s) (pair_mem_pairList grid s)
      change min (supportWall U (unitNormal t) x) (supportWall U (companionNormal t) x) ≤ _ at hsource
      rw [supportWall_unitNormal, supportWall_companionNormal] at hsource
      exact max_le hsource (finiteNiche_nonneg _ _ _ _)

end AngularGrid

end AmbidextrousSofa
