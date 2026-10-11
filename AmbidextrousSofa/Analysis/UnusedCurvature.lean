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
  rcases i with _ | t | t
  · exact Ioo_subset_Icc_self (affineNormalAngle_mem m)
  all_goals
    simp only [partialCapAngle, usedNormalAngle, Sum.elim_inl, Sum.elim_inr, mem_Icc]
    constructor <;> linarith [t.2.1, t.2.2, Real.pi_pos]

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
  have key : coordDot p (unitNormal (affineNormalAngle m)) ≤ c * Real.cos (Real.arctan m) ↔
      p.2 ≤ m * p.1 + c := mem_affine_halfMinus_iff p m c
  simp only [capCut, mem_inter_iff, mem_ofPred_eq, mem_usedSupportSaturation_iff,
    FinitePolygon.mem_upperPolygon_iff, Option.forall, Sum.forall, Subtype.forall,
    partialCapAngle, partialCapHeight, usedNormalAngle, usedNormal, Sum.elim_inl, Sum.elim_inr,
    ← companionNormal_eq_unitNormal, key, imp_and, forall_and]
  tauto

def unusedNormalIntervals (α : ℝ) : Set ℝ :=
  Ioo α (Real.pi / 2) ∪ Ioo (α + Real.pi / 2) Real.pi

theorem partialCapAngle_eq_middle_of_mem_unused {α m : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2)
    (i : Fin 4 ⊕ Option (Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α))
    (hi : FinitePolygon.fullPolygonAngle (partialCapAngle α m) i ∈ unusedNormalIntervals α) :
    FinitePolygon.fullPolygonAngle (partialCapAngle α m) i = affineNormalAngle m := by
  rcases i with i | _ | t | t
  · fin_cases i <;> rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [FinitePolygon.fullPolygonAngle, Fin.reduceFinMk, Matrix.cons_val] at h1 h2 <;>
      linarith [Real.pi_pos]
  · rfl
  all_goals
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [FinitePolygon.fullPolygonAngle, partialCapAngle, usedNormalAngle, Sum.elim_inl,
        Sum.elim_inr] at h1 h2 <;> linarith [t.2.1, t.2.2, Real.pi_pos]

end AmbidextrousSofa
