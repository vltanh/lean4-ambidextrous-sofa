module

public import AmbidextrousSofa.Analysis.GridScore

@[expose] public section

/-!
# Persistent selection weights on the actual dyadic walls

Each earlier dyadic source keeps a positive weight at every later stage.
Repeated occurrences of the same geometric wall are combined into its
single actual source index. The total weight is at most one. Thus the
penalty has the existing polygon derivative, while a vanishing penalty
forces agreement at every fixed sample, not just at the current grid.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι κ : Type*}

def aggregateWeight [Fintype κ] [DecidableEq ι]
    (source : κ → ι) (weight : κ → ℝ) (i : ι) : ℝ :=
  ∑ s, if source s = i then weight s else 0

theorem aggregateWeight_nonneg [Fintype κ] [DecidableEq ι]
    (source : κ → ι) (weight : κ → ℝ) (hw : ∀ s, 0 ≤ weight s) (i : ι) :
    0 ≤ aggregateWeight source weight i :=
  Finset.sum_nonneg fun s _ => ite_nonneg (hw s) le_rfl

theorem sum_aggregateWeight [Fintype ι] [Fintype κ] [DecidableEq ι]
    (source : κ → ι) (weight : κ → ℝ) :
    ∑ i, aggregateWeight source weight i = ∑ s, weight s := by
  unfold aggregateWeight; rw [Finset.sum_comm]; simp

theorem heightPenalty_aggregate [Fintype ι] [Fintype κ] [DecidableEq ι]
    (source : κ → ι) (weight : κ → ℝ) (target height : ι → ℝ) :
    heightPenalty (aggregateWeight source weight) target height =
      ∑ s, weight s * (height (source s) - target (source s)) ^ 2 := by
  simp only [heightPenalty, aggregateWeight, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem sampledPenalty_mul [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (weight target : ι → ℝ) (c : ℝ) :
    sampledPenalty U normal (fun i => c * weight i) target =
      c * sampledPenalty U normal weight target := by
  simp [sampledPenalty, heightPenalty, Finset.mul_sum, mul_assoc]

end FinitePolygon

namespace AngularGrid

open FinitePolygon

def liftInterior {grid other : Finset QuarterAngle} (h : grid ⊆ other)
    (t : InteriorPoint grid) : InteriorPoint other := by
  classical
  exact ⟨t.val, Finset.mem_filter.mpr
    ⟨h (interiorPoint_mem_grid grid t), interiorPoint_mem grid t⟩⟩

def liftSource {grid other : Finset QuarterAngle} (h : grid ⊆ other) :
    SourceIndex grid → SourceIndex other
  | Sum.inl t => Sum.inl (liftInterior h t)
  | Sum.inr t => Sum.inr (liftInterior h t)

theorem normal_liftSource {grid other : Finset QuarterAngle} (h : grid ⊆ other)
    (i : SourceIndex grid) : normal other (liftSource h i) = normal grid i := by
  cases i <;> rfl

abbrev SampleIndex (n : ℕ) := Σ m : Fin (n + 1), SourceIndex (dyadic m.val)

def sampleSource (n : ℕ) (s : SampleIndex n) : SourceIndex (dyadic n) :=
  liftSource (dyadic_mono (Nat.lt_succ_iff.mp s.1.isLt)) s.2

def levelWeight (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (m + 1) / (Fintype.card (SourceIndex (dyadic m)) + 1)

theorem levelWeight_pos (m : ℕ) : 0 < levelWeight m := by
  unfold levelWeight; positivity

def sampleWeight (n : ℕ) (s : SampleIndex n) : ℝ := levelWeight s.1.val

def stageWeight (n : ℕ) : SourceIndex (dyadic n) → ℝ := by
  classical
  exact aggregateWeight (sampleSource n) (sampleWeight n)

theorem stageWeight_nonneg (n : ℕ) (i : SourceIndex (dyadic n)) :
    0 ≤ stageWeight n i := by
  classical exact aggregateWeight_nonneg _ _ (fun _ => (levelWeight_pos _).le) i

theorem sum_stageWeight_le_one (n : ℕ) :
    (∑ i, stageWeight n i) ≤ 1 := by
  classical
  rw [stageWeight, sum_aggregateWeight, Fintype.sum_sigma]
  refine (Finset.sum_le_sum fun (m : Fin (n + 1)) _ => (?_ :
    ∑ _i : SourceIndex (dyadic m.val), levelWeight m.val ≤ (1 / 2 : ℝ) ^ (m.val + 1))).trans ?_
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, levelWeight, mul_div_left_comm]
    exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (by linarith) (by positivity))
  · rw [Fin.sum_univ_eq_sum_range (fun m => (1 / 2 : ℝ) ^ (m + 1))]
    simp_rw [pow_succ, ← Finset.sum_mul]
    linarith [sum_geometric_two_le (n + 1)]

def stagePenalty (n : ℕ) (target U : Set Plane) : ℝ :=
  sampledPenalty U (normal (dyadic n)) (stageWeight n)
    (fun i => support target (normal (dyadic n) i))

/-- Every old sample retains a strictly positive coefficient in the
actual current-wall penalty. -/
theorem persistent_sample_bound {m n : ℕ} (hmn : m ≤ n)
    (i : SourceIndex (dyadic m)) (target U : Set Plane) :
    levelWeight m *
      (support U (normal (dyadic m) i) - support target (normal (dyadic m) i)) ^ 2 ≤
        stagePenalty n target U := by
  classical
  simp only [stagePenalty, sampledPenalty, stageWeight, heightPenalty_aggregate, sampleSource,
    normal_liftSource, sampleWeight]
  exact Finset.single_le_sum (f := fun s : SampleIndex n => levelWeight s.1.val *
      (support U (normal (dyadic s.1.val) s.2) - support target (normal (dyadic s.1.val) s.2)) ^ 2)
    (fun s _ => mul_nonneg (levelWeight_pos _).le (sq_nonneg _))
    (Finset.mem_univ ⟨⟨m, Nat.lt_succ_iff.mpr hmn⟩, i⟩)

theorem stagePenalty_self (n : ℕ) (U : Set Plane) : stagePenalty n U U = 0 := by
  simp [stagePenalty, sampledPenalty, heightPenalty]

def selectionRate (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem selectionRate_pos (n : ℕ) : 0 < selectionRate n := Nat.one_div_pos_of_nat

theorem selectionRate_tendsto : Tendsto selectionRate atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end AngularGrid

end AmbidextrousSofa
