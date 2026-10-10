import AmbidextrousSofa.Analysis.PartialGridNiche
import AmbidextrousSofa.Analysis.PersistentPenalty

/-!
# Actual partial-grid polygons and their terminal source

The outer grid contains the original dyadic samples, their rescaled
visited samples, and the terminal normal. Finsets identify coincident
normals, so the physical affine slopes remain distinct. Only the rescaled
open samples supply paired corners. The whole terminal first wall has its
own existing normal index and retains the exact outgoing constraint.

Old persistent penalty weights are aggregated onto these actual indices.
This keeps the same support-separating penalty and its total weight bound,
including outer-only sampled directions in the unused arcs.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon

def terminalQuarterAngle (α : TerminalAngle) : AngularGrid.QuarterAngle :=
  ⟨α, α.pos.le, α.property.2⟩

def outerGrid (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    Finset AngularGrid.QuarterAngle := by
  classical
  exact insert (terminalQuarterAngle α) (grid ∪ grid.image (scaleAngle α))

theorem subset_outerGrid (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    grid ⊆ outerGrid α grid := by
  classical
  exact Finset.subset_insert_of_subset _ (Finset.subset_union_left)

theorem scaled_mem_outerGrid (α : TerminalAngle) {grid : Finset AngularGrid.QuarterAngle}
    {t : AngularGrid.QuarterAngle} (ht : t ∈ grid) : scaleAngle α t ∈ outerGrid α grid := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))

theorem terminal_mem_outerGrid (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    terminalQuarterAngle α ∈ outerGrid α grid := by
  classical
  exact Finset.mem_insert_self _ _

abbrev SourceIndex (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :=
  AngularGrid.SourceIndex (outerGrid α grid)

def normal (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    SourceIndex α grid → Plane := AngularGrid.normal (outerGrid α grid)

def fullAngle (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    SourceIndex α grid → ℝ := AngularGrid.fullAngle (outerGrid α grid)

def scaledInterior (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    (t : AngularGrid.InteriorPoint grid) : AngularGrid.InteriorPoint (outerGrid α grid) := by
  classical
  have ht := scaleAngle_mem_open α (AngularGrid.interiorPoint_mem grid t)
  exact ⟨scaleAngle α t.val, Finset.mem_filter.mpr
    ⟨scaled_mem_outerGrid α (AngularGrid.interiorPoint_mem_grid grid t),
      ht.1, ht.2.trans_le α.property.2⟩⟩

def terminalIndex (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) : SourceIndex α grid := by
  classical
  exact Sum.inl ⟨terminalQuarterAngle α, Finset.mem_filter.mpr
    ⟨terminal_mem_outerGrid α grid, α.pos, hαL⟩⟩

def pairList (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    List (SourceIndex α grid × SourceIndex α grid) := by
  classical
  exact (Finset.univ : Finset (AngularGrid.InteriorPoint grid)).toList.map
    (fun t => (Sum.inl (scaledInterior α grid t), Sum.inr (scaledInterior α grid t)))

theorem pair_mem_pairList (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    (t : AngularGrid.InteriorPoint grid) :
    (Sum.inl (scaledInterior α grid t), Sum.inr (scaledInterior α grid t)) ∈ pairList α grid := by
  classical
  exact List.mem_map.mpr ⟨t, by simp, rfl⟩

theorem normal_eq_unitNormal (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    (i : SourceIndex α grid) : normal α grid i = unitNormal (fullAngle α grid i) :=
  AngularGrid.normal_eq_unitNormal (outerGrid α grid) i

theorem normal_snd_pos (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    (i : SourceIndex α grid) : 0 < (normal α grid i).2 :=
  AngularGrid.normal_snd_pos (outerGrid α grid) i

theorem normal_fst_ne_zero (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    (i : SourceIndex α grid) : (normal α grid i).1 ≠ 0 :=
  AngularGrid.normal_fst_ne_zero (outerGrid α grid) i

theorem normal_unit (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    (i : SourceIndex α grid) : coordDot (normal α grid i) (normal α grid i) = 1 :=
  AngularGrid.normal_unit (outerGrid α grid) i

theorem wallSlopes_injective (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    Function.Injective (wallSlope (normal α grid)) :=
  AngularGrid.wallSlopes_injective (outerGrid α grid)

theorem normal_terminalIndex (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) :
    normal α grid (terminalIndex α hαL grid) = unitNormal α := rfl

theorem scaleAngle_of_top (α : TerminalAngle) {t : AngularGrid.QuarterAngle}
    (ht : (t : ℝ) = Real.pi / 2) : (scaleAngle α t : ℝ) = (α : ℝ) := by
  simp only [scaleAngle, unitParameter, ht,
    div_self (by linarith [Real.pi_pos] : Real.pi / 2 ≠ 0), mul_one]

/-- Every actual physical corner is sampled strictly before the retained
terminal angle. There is no reflected outgoing family. -/
theorem pairList_visited (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    {ij : SourceIndex α grid × SourceIndex α grid} (hij : ij ∈ pairList α grid) :
    ∃ θ ∈ Ioo (0 : ℝ) (α : ℝ), normal α grid ij.1 = unitNormal θ ∧
      normal α grid ij.2 = companionNormal θ := by
  classical
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hij
  exact ⟨scaleAngle α t.val, scaleAngle_mem_open α (AngularGrid.interiorPoint_mem grid t),
    rfl, rfl⟩

theorem finiteBarrier_eq_barrier (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset AngularGrid.QuarterAngle) (x : ℝ) :
    finiteBarrier U (normal α grid) (pairList α grid)
      (some (terminalIndex α hαL grid)) x = barrier U α grid x := by
  classical
  change max (finiteNiche U (normal α grid) (pairList α grid) x)
    (supportWall U (normal α grid (terminalIndex α hαL grid)) x) = _
  rw [normal_terminalIndex, supportWall_unitNormal]
  change max (finiteNiche U (normal α grid) (pairList α grid) x) (firstWall U α x) =
    max (niche U α grid x) (firstWall U α x)
  apply le_antisymm
  · apply max_le _ (le_max_right _ _)
    apply (finiteNiche_le_iff U (normal α grid) (pairList α grid) x _).mpr
    refine ⟨(niche_nonneg U α grid x).trans (le_max_left _ _), ?_⟩
    intro ij hij
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hij
    change min (supportWall U (unitNormal (scaleAngle α t.val)) x)
      (supportWall U (companionNormal (scaleAngle α t.val)) x) ≤ _
    rw [supportWall_unitNormal, supportWall_companionNormal]
    exact (le_max_left _ _).trans ((clip_le_niche U α grid x
      (AngularGrid.interiorPoint_mem_grid grid t)).trans (le_max_left _ _))
  · apply max_le _ (le_max_right _ _)
    apply (niche_le_iff U α grid x _).mpr
    refine ⟨(finiteNiche_nonneg _ _ _ _).trans (le_max_left _ _), ?_⟩
    intro t ht
    by_cases ht0 : (t : ℝ) = 0
    · have hscale : (scaleAngle α t : ℝ) = 0 := by
        simp only [scaleAngle, unitParameter, ht0, zero_div, mul_zero]
      rw [hscale]
      have hfirst : firstWall U 0 x = 0 := by simp [firstWall]
      exact max_le (((min_le_left _ _).trans hfirst.le).trans
        ((finiteNiche_nonneg _ _ _ _).trans (le_max_left _ _)))
        ((finiteNiche_nonneg _ _ _ _).trans (le_max_left _ _))
    by_cases htL : (t : ℝ) = Real.pi / 2
    · rw [scaleAngle_of_top α htL]
      exact max_le ((min_le_left _ _).trans (le_max_right _ _))
        ((finiteNiche_nonneg _ _ _ _).trans (le_max_left _ _))
    · have htopen : 0 < (t : ℝ) ∧ (t : ℝ) < Real.pi / 2 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 htL⟩
      let s : AngularGrid.InteriorPoint grid := ⟨t, Finset.mem_filter.mpr ⟨ht, htopen⟩⟩
      have hsource := ((finiteNiche_le_iff U (normal α grid) (pairList α grid) x _).mp
        (le_refl (finiteNiche U (normal α grid) (pairList α grid) x))).2
          (Sum.inl (scaledInterior α grid s), Sum.inr (scaledInterior α grid s))
          (pair_mem_pairList α grid s)
      change min (supportWall U (unitNormal (scaleAngle α t)) x)
        (supportWall U (companionNormal (scaleAngle α t)) x) ≤ _ at hsource
      rw [supportWall_unitNormal, supportWall_companionNormal] at hsource
      exact max_le (hsource.trans (le_max_left _ _))
        ((finiteNiche_nonneg _ _ _ _).trans (le_max_left _ _))

def stageWeight (α : TerminalAngle) (n : ℕ) : SourceIndex α (AngularGrid.dyadic n) → ℝ := by
  classical
  exact aggregateWeight (AngularGrid.liftSource (subset_outerGrid α (AngularGrid.dyadic n)))
    (AngularGrid.stageWeight n)

theorem stageWeight_nonneg (α : TerminalAngle) (n : ℕ)
    (i : SourceIndex α (AngularGrid.dyadic n)) : 0 ≤ stageWeight α n i := by
  classical
  exact aggregateWeight_nonneg _ _ (AngularGrid.stageWeight_nonneg n) i

theorem sum_stageWeight_le_one (α : TerminalAngle) (n : ℕ) :
    (∑ i, stageWeight α n i) ≤ 1 := by
  classical
  rw [stageWeight, sum_aggregateWeight]
  exact AngularGrid.sum_stageWeight_le_one n

/-- Adding the actual terminal and rescaled normals changes the index
type, but leaves the old support-separating penalty exactly unchanged. -/
theorem sampledPenalty_eq_stagePenalty (α : TerminalAngle) (n : ℕ)
    (target U : Set Plane) :
    sampledPenalty U (normal α (AngularGrid.dyadic n)) (stageWeight α n)
      (fun i => support target (normal α (AngularGrid.dyadic n) i)) =
        AngularGrid.stagePenalty n target U := by
  classical
  unfold sampledPenalty stageWeight
  rw [heightPenalty_aggregate]
  simp only [normal, AngularGrid.normal_liftSource]
  rfl

end PartialGrid

end AmbidextrousSofa
