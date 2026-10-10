module

public import AmbidextrousSofa.Analysis.UsedSupportSaturation
public import AmbidextrousSofa.Analysis.DiscreteCurvature
public import AmbidextrousSofa.Analysis.AffineNormal

@[expose] public section

/-!
# Actual curvature on the unvisited normal intervals

The exact used-support and affine-ceiling representation is a literal
intersection of halfplanes. Its defining directions omit both unvisited
open intervals, except possibly the single normal of the middle ceiling.
The actual halfplane-gap corner theorem therefore makes the support vertex
constant on every remaining gap. Its Stieltjes surface-area measure is zero
there. Terminal directions themselves remain outside these open intervals,
so their possible atoms have not been discarded.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def usedNormalAngle (α : ℝ) : Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α → ℝ :=
  Sum.elim (fun t => t) (fun t => (t : ℝ) + Real.pi / 2)

theorem usedNormal_eq_unitNormal (α : ℝ) (i : Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α) :
    usedNormal α i = unitNormal (usedNormalAngle α i) := by
  rcases i with t | t
  · rfl
  · exact companionNormal_eq_unitNormal t

theorem usedNormalAngle_mem {α : ℝ} (hα : α ≤ Real.pi / 2)
    (i : Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α) : usedNormalAngle α i ∈ Icc 0 Real.pi := by
  rcases i with t | t
  · change 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ Real.pi
    exact ⟨t.property.1, by linarith [t.property.2, Real.pi_pos]⟩
  · change 0 ≤ (t : ℝ) + Real.pi / 2 ∧ (t : ℝ) + Real.pi / 2 ≤ Real.pi
    constructor <;> linarith [t.property.1, t.property.2, Real.pi_pos]

def partialCapAngle (α m : ℝ) : Option (Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α) → ℝ
  | none => affineNormalAngle m
  | some i => usedNormalAngle α i

def partialCapHeight (U : Set Plane) (α m c : ℝ) :
    Option (Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α) → ℝ
  | none => c * Real.cos (Real.arctan m)
  | some i => support U (usedNormal α i)

theorem partialCapAngle_mem {α : ℝ} (hα : α ≤ Real.pi / 2) (m : ℝ)
    (i : Option (Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α)) :
    partialCapAngle α m i ∈ Icc 0 Real.pi := by
  cases i with
  | none => exact ⟨(affineNormalAngle_mem m).1.le, (affineNormalAngle_mem m).2.le⟩
  | some i => exact usedNormalAngle_mem hα i

/-- This is the full literal halfplane representation: the four box walls,
every used first and second support, and the single affine middle ceiling. -/
theorem capCut_usedSupportSaturation_eq_halfplanes (U : Set Plane) (α m c : ℝ) :
    capCut (usedSupportSaturation U α) (fun x => m * x + c) =
      ⋂ i, MovingSofaOptimality.halfMinus
        (FinitePolygon.fullPolygonAngle (partialCapAngle α m) i)
        (FinitePolygon.fullPolygonHeight (horizontalLeft U) (horizontalRight U)
          (partialCapHeight U α m c) i) := by
  rw [← FinitePolygon.upperPolygon_eq_iInter_halfMinus]
  ext p
  rw [FinitePolygon.mem_upperPolygon_iff]
  change (p ∈ usedSupportSaturation U α ∧ p.2 ≤ m * p.1 + c) ↔ _
  rw [mem_usedSupportSaturation_iff]
  constructor
  · rintro ⟨⟨hx, hy, hused⟩, hline⟩
    refine ⟨hx, hy, ?_⟩
    intro i
    cases i with
    | none => exact (mem_affine_halfMinus_iff p m c).mpr hline
    | some i =>
      change coordDot p (unitNormal (usedNormalAngle α i)) ≤ support U (usedNormal α i)
      rw [← usedNormal_eq_unitNormal]
      rcases i with t | t
      · exact (hused t t.property).1
      · exact (hused t t.property).2
  · rintro ⟨hx, hy, hhalf⟩
    refine ⟨⟨hx, hy, ?_⟩, (mem_affine_halfMinus_iff p m c).mp (hhalf none)⟩
    intro t ht
    constructor
    · have h := hhalf (some (Sum.inl ⟨t, ht⟩))
      exact h
    · have h := hhalf (some (Sum.inr ⟨t, ht⟩))
      change coordDot p (unitNormal (t + Real.pi / 2)) ≤ support U (companionNormal t) at h
      rwa [← companionNormal_eq_unitNormal] at h

def unusedNormalIntervals (α : ℝ) : Set ℝ :=
  Ioo α (Real.pi / 2) ∪ Ioo (α + Real.pi / 2) Real.pi

theorem partialCapAngle_eq_middle_of_mem_unused {α m : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2)
    (i : Fin 4 ⊕ Option (Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α))
    (hi : FinitePolygon.fullPolygonAngle (partialCapAngle α m) i ∈ unusedNormalIntervals α) :
    FinitePolygon.fullPolygonAngle (partialCapAngle α m) i = affineNormalAngle m := by
  cases i with
  | inl i =>
    fin_cases i
    · change (0 : ℝ) ∈ unusedNormalIntervals α at hi
      rcases hi with hi | hi <;> exfalso <;> linarith [hi.1, hi.2, Real.pi_pos]
    · change Real.pi / 2 ∈ unusedNormalIntervals α at hi
      rcases hi with hi | hi <;> exfalso <;> linarith [hi.1, hi.2, Real.pi_pos]
    · change Real.pi ∈ unusedNormalIntervals α at hi
      rcases hi with hi | hi <;> exfalso <;> linarith [hi.1, hi.2, Real.pi_pos]
    · change 3 * Real.pi / 2 ∈ unusedNormalIntervals α at hi
      rcases hi with hi | hi <;> exfalso <;> linarith [hi.1, hi.2, Real.pi_pos]
  | inr i =>
    cases i with
    | none => rfl
    | some i =>
      rcases i with t | t
      · change (t : ℝ) ∈ Ioo α (Real.pi / 2) ∪ Ioo (α + Real.pi / 2) Real.pi at hi
        rcases hi with hi | hi <;> exfalso <;>
          linarith [hi.1, hi.2, t.property.1, t.property.2, Real.pi_pos]
      · change (t : ℝ) + Real.pi / 2 ∈ Ioo α (Real.pi / 2) ∪
          Ioo (α + Real.pi / 2) Real.pi at hi
        rcases hi with hi | hi <;> exfalso <;>
          linarith [hi.1, hi.2, t.property.1, t.property.2, Real.pi_pos]

end AmbidextrousSofa
