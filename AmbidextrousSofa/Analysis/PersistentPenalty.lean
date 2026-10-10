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
    0 ≤ aggregateWeight source weight i := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact hw s
  · exact le_rfl

theorem sum_aggregateWeight [Fintype ι] [Fintype κ] [DecidableEq ι]
    (source : κ → ι) (weight : κ → ℝ) :
    ∑ i, aggregateWeight source weight i = ∑ s, weight s := by
  unfold aggregateWeight
  rw [Finset.sum_comm]
  simp

theorem heightPenalty_aggregate [Fintype ι] [Fintype κ] [DecidableEq ι]
    (source : κ → ι) (weight : κ → ℝ) (target height : ι → ℝ) :
    heightPenalty (aggregateWeight source weight) target height =
      ∑ s, weight s * (height (source s) - target (source s)) ^ 2 := by
  unfold heightPenalty aggregateWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [ite_mul]

theorem sampledPenalty_nonneg [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (weight target : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) :
    0 ≤ sampledPenalty U normal weight target := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

theorem sampledPenalty_mul [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (weight target : ι → ℝ) (c : ℝ) :
    sampledPenalty U normal (fun i => c * weight i) target =
      c * sampledPenalty U normal weight target := by
  unfold sampledPenalty heightPenalty
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sampledPenalty_self [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (weight : ι → ℝ) :
    sampledPenalty U normal weight (fun i => support U (normal i)) = 0 := by
  simp [sampledPenalty, heightPenalty]

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
  unfold levelWeight
  positivity

def sampleWeight (n : ℕ) (s : SampleIndex n) : ℝ := levelWeight s.1.val

def stageWeight (n : ℕ) : SourceIndex (dyadic n) → ℝ := by
  classical
  exact aggregateWeight (sampleSource n) (sampleWeight n)

theorem stageWeight_nonneg (n : ℕ) (i : SourceIndex (dyadic n)) :
    0 ≤ stageWeight n i := by
  classical
  exact aggregateWeight_nonneg (sampleSource n) (sampleWeight n)
    (fun s => (levelWeight_pos s.1.val).le) i

theorem sum_levelWeight_le (m : ℕ) :
    (∑ _i : SourceIndex (dyadic m), levelWeight m) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
  have hd : (0 : ℝ) < Fintype.card (SourceIndex (dyadic m)) + 1 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold levelWeight
  rw [← mul_div_assoc, div_le_iff₀ hd]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
  nlinarith

theorem sum_half_pow (n : ℕ) :
    (∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ (m + 1)) = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem sum_stageWeight_le_one (n : ℕ) :
    (∑ i, stageWeight n i) ≤ 1 := by
  classical
  rw [stageWeight, sum_aggregateWeight, Fintype.sum_sigma]
  calc
    (∑ m : Fin (n + 1), ∑ _i : SourceIndex (dyadic m.val), levelWeight m.val) ≤
        ∑ m : Fin (n + 1), (1 / 2 : ℝ) ^ (m.val + 1) :=
      Finset.sum_le_sum (fun m _ => sum_levelWeight_le m.val)
    _ = 1 - (1 / 2 : ℝ) ^ (n + 1) := by
      exact (Fin.sum_univ_eq_sum_range (fun m => (1 / 2 : ℝ) ^ (m + 1)) (n + 1)).trans
        (sum_half_pow (n + 1))
    _ ≤ 1 := sub_le_self _ (by positivity)

def stagePenalty (n : ℕ) (target U : Set Plane) : ℝ :=
  sampledPenalty U (normal (dyadic n)) (stageWeight n)
    (fun i => support target (normal (dyadic n) i))

theorem stagePenalty_nonneg (n : ℕ) (target U : Set Plane) :
    0 ≤ stagePenalty n target U :=
  sampledPenalty_nonneg _ _ _ _ (stageWeight_nonneg n)

theorem stagePenalty_eq_sum (n : ℕ) (target U : Set Plane) :
    stagePenalty n target U = ∑ s : SampleIndex n,
      levelWeight s.1.val *
        (support U (normal (dyadic s.1.val) s.2) -
          support target (normal (dyadic s.1.val) s.2)) ^ 2 := by
  classical
  unfold stagePenalty sampledPenalty stageWeight
  rw [heightPenalty_aggregate]
  apply Finset.sum_congr rfl
  intro s _
  simp only [sampleSource, normal_liftSource, sampleWeight]

/-- Every old sample retains a strictly positive coefficient in the
actual current-wall penalty. -/
theorem persistent_sample_bound {m n : ℕ} (hmn : m ≤ n)
    (i : SourceIndex (dyadic m)) (target U : Set Plane) :
    levelWeight m *
      (support U (normal (dyadic m) i) - support target (normal (dyadic m) i)) ^ 2 ≤
        stagePenalty n target U := by
  classical
  rw [stagePenalty_eq_sum]
  let s : SampleIndex n := ⟨⟨m, Nat.lt_succ_iff.mpr hmn⟩, i⟩
  have h := Finset.single_le_sum (f := fun s : SampleIndex n => levelWeight s.1.val *
      (support U (normal (dyadic s.1.val) s.2) - support target (normal (dyadic s.1.val) s.2)) ^ 2)
    (fun s _ => mul_nonneg (levelWeight_pos s.1.val).le (sq_nonneg _))
    (Finset.mem_univ s)
  exact h

theorem stagePenalty_self (n : ℕ) (U : Set Plane) : stagePenalty n U U = 0 :=
  sampledPenalty_self U (normal (dyadic n)) (stageWeight n)

def selectionRate (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem selectionRate_pos (n : ℕ) : 0 < selectionRate n := by
  unfold selectionRate
  positivity

theorem selectionRate_tendsto : Tendsto selectionRate atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end AngularGrid

end AmbidextrousSofa
