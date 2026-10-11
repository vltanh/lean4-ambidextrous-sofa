module

public import AmbidextrousSofa.Analysis.PartialGridNiche
public import AmbidextrousSofa.Analysis.PersistentPenalty

@[expose] public section

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
  ⟨α, (TerminalAngle.pos α).le, α.property.2⟩

def outerGrid (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    Finset AngularGrid.QuarterAngle := by
  classical
  exact insert (terminalQuarterAngle α) (grid ∪ grid.image (scaleAngle α))

theorem subset_outerGrid (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    grid ⊆ outerGrid α grid :=
  Finset.subset_union_left.trans (Finset.subset_insert _ _)

theorem scaled_mem_outerGrid (α : TerminalAngle) {grid : Finset AngularGrid.QuarterAngle}
    {t : AngularGrid.QuarterAngle} (ht : t ∈ grid) : scaleAngle α t ∈ outerGrid α grid :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))

theorem terminal_mem_outerGrid (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    terminalQuarterAngle α ∈ outerGrid α grid :=
  Finset.mem_insert_self _ _

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
    ⟨terminal_mem_outerGrid α grid, (TerminalAngle.pos α), hαL⟩⟩

def pairList (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle) :
    List (SourceIndex α grid × SourceIndex α grid) := by
  classical
  exact (Finset.univ : Finset (AngularGrid.InteriorPoint grid)).toList.map
    (fun t => (Sum.inl (scaledInterior α grid t), Sum.inr (scaledInterior α grid t)))

theorem pair_mem_pairList (α : TerminalAngle) (grid : Finset AngularGrid.QuarterAngle)
    (t : AngularGrid.InteriorPoint grid) :
    (Sum.inl (scaledInterior α grid t), Sum.inr (scaledInterior α grid t)) ∈ pairList α grid :=
  List.mem_map.mpr ⟨t, by simp, rfl⟩

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

theorem finiteBarrier_eq_barrier (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset AngularGrid.QuarterAngle) (x : ℝ) :
    finiteBarrier U (normal α grid) (pairList α grid)
      (some (terminalIndex α hαL grid)) x = barrier U α grid x := by
  have hwall (θ : ℝ) : min (supportWall U (unitNormal θ) x)
      (supportWall U (companionNormal θ) x) = cornerWall U θ x := by
    rw [supportWall_unitNormal, supportWall_companionNormal, cornerWall]
  have h0 := (finiteNiche_nonneg U (normal α grid) (pairList α grid) x).trans
    (le_max_left _ (firstWall U α x))
  refine le_antisymm (max_le_max ?_ le_rfl) (max_le ?_ (le_max_right _ _))
  · refine (finiteNiche_le_iff _ _ _ x _).2 ⟨niche_nonneg U α grid x, fun ij hij => ?_⟩
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hij
    exact (hwall _).trans_le ((le_max_left _ _).trans
      (clip_le_niche U α grid x (AngularGrid.interiorPoint_mem_grid grid t)))
  refine (niche_le_iff U α grid x _).2 ⟨h0, fun t ht => max_le ?_ h0⟩
  rcases t.property.1.eq_or_lt with ht0 | ht0
  · refine (min_le_left _ _).trans (le_trans (le_of_eq ?_) h0)
    simp [scaleAngle, unitParameter, ← ht0, firstWall]
  rcases t.property.2.lt_or_eq with htL | htL
  · rw [← hwall]
    exact (((finiteNiche_le_iff U (normal α grid) (pairList α grid) x _).1 le_rfl).2 _
      (pair_mem_pairList α grid ⟨t, Finset.mem_filter.mpr ⟨ht, ht0, htL⟩⟩)).trans
      (le_max_left _ _)
  · have : (scaleAngle α t : ℝ) = α := by simp [scaleAngle, unitParameter, htL]
    exact this ▸ (min_le_left _ _).trans (le_max_right _ _)

def stageWeight (α : TerminalAngle) (n : ℕ) : SourceIndex α (AngularGrid.dyadic n) → ℝ := by
  classical
  exact aggregateWeight (AngularGrid.liftSource (subset_outerGrid α (AngularGrid.dyadic n)))
    (AngularGrid.stageWeight n)

theorem stageWeight_nonneg (α : TerminalAngle) (n : ℕ)
    (i : SourceIndex α (AngularGrid.dyadic n)) : 0 ≤ stageWeight α n i :=
  aggregateWeight_nonneg _ _ (AngularGrid.stageWeight_nonneg n) i

theorem sum_stageWeight_le_one (α : TerminalAngle) (n : ℕ) :
    (∑ i, stageWeight α n i) ≤ 1 :=
  (sum_aggregateWeight _ _).trans_le (AngularGrid.sum_stageWeight_le_one n)

/-- Adding the actual terminal and rescaled normals changes the index
type, but leaves the old support-separating penalty exactly unchanged. -/
theorem sampledPenalty_eq_stagePenalty (α : TerminalAngle) (n : ℕ)
    (target U : Set Plane) :
    sampledPenalty U (normal α (AngularGrid.dyadic n)) (stageWeight α n)
      (fun i => support target (normal α (AngularGrid.dyadic n) i)) =
        AngularGrid.stagePenalty n target U := by
  simp only [sampledPenalty, stageWeight, heightPenalty_aggregate, normal,
    AngularGrid.normal_liftSource]
  rfl

end PartialGrid

end AmbidextrousSofa
