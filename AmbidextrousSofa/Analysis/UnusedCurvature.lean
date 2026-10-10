import AmbidextrousSofa.Analysis.UsedSupportSaturation
import AmbidextrousSofa.Analysis.DiscreteCurvature
import AmbidextrousSofa.Analysis.AffineNormal

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
  · exact ⟨t.property.1, by linarith [t.property.2, Real.pi_pos]⟩
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
      ⋂ i, Imported.halfMinus
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
      simpa only [partialCapAngle, partialCapHeight, usedNormalAngle, usedNormal,
        ← companionNormal_eq_unitNormal] using h

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

/-- A single allowed exceptional normal leaves two genuine zero-curvature
gaps; the exceptional singleton itself is retained. -/
theorem sigma_Ioo_diff_singleton_eq_zero_of_halfplane_gap {K : Set Plane}
    (hK : Imported.IsConvexBody K) {ι : Type*} (angle height : ι → ℝ)
    (hpoly : K = ⋂ i, Imported.halfMinus (angle i) (height i))
    (hangle : ∀ i, angle i ∈ Icc 0 (2 * Real.pi))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi) (hab : a < b) (hspan : b - a < Real.pi)
    (hgap : ∀ i, angle i ∈ Ioo a b → angle i = c) :
    Imported.sigma K (Ioo a b \ {c}) = 0 := by
  by_cases hca : c ≤ a
  · apply measure_mono_null sdiff_subset
    apply sigma_Ioo_eq_zero_of_halfplane_gap hK angle height hpoly hangle ha hb hab hspan
    intro i hi
    have heq := hgap i hi
    linarith [hi.1]
  by_cases hbc : b ≤ c
  · apply measure_mono_null sdiff_subset
    apply sigma_Ioo_eq_zero_of_halfplane_gap hK angle height hpoly hangle ha hb hab hspan
    intro i hi
    have heq := hgap i hi
    linarith [hi.2]
  · have hac : a < c := lt_of_not_ge hca
    have hcb : c < b := lt_of_not_ge hbc
    rw [← Ioo_union_Ioo_eq_Ioo_sdiff_singleton hac.le hcb.le]
    apply measure_union_null
    · apply sigma_Ioo_eq_zero_of_halfplane_gap hK angle height hpoly hangle
        ha (hcb.le.trans hb) hac (by linarith)
      intro i hi
      have heq := hgap i ⟨hi.1, hi.2.trans hcb⟩
      linarith [hi.2]
    · apply sigma_Ioo_eq_zero_of_halfplane_gap hK angle height hpoly hangle
        (ha.trans hac.le) hb hcb (by linarith)
      intro i hi
      have heq := hgap i ⟨hac.trans hi.1, hi.2⟩
      linarith [hi.1]

theorem upperCurvature_unused_of_usedSupportSaturation_capCut
    {U V : Set Plane} {α m c : ℝ} (hV : IsDownwardCap V)
    (hα0 : 0 ≤ α) (hα : α < Real.pi / 2)
    (hcut : V = capCut (usedSupportSaturation U α) (fun x => m * x + c)) :
    upperCurvature V (unusedNormalIntervals α \ {affineNormalAngle m}) = 0 := by
  let angle := FinitePolygon.fullPolygonAngle (partialCapAngle α m)
  let height := FinitePolygon.fullPolygonHeight (horizontalLeft U) (horizontalRight U)
    (partialCapHeight U α m c)
  have hpoly : V = ⋂ i, Imported.halfMinus (angle i) (height i) :=
    hcut.trans (capCut_usedSupportSaturation_eq_halfplanes U α m c)
  have hangle : ∀ i, angle i ∈ Icc 0 (2 * Real.pi) :=
    FinitePolygon.fullPolygonAngle_mem _ (partialCapAngle_mem hα.le m)
  unfold unusedNormalIntervals
  rw [union_sdiff_distrib]
  apply measure_union_null
  · apply sigma_Ioo_diff_singleton_eq_zero_of_halfplane_gap hV.imported_isConvexBody
      angle height hpoly hangle hα0 (by linarith [Real.pi_pos]) hα (by linarith [Real.pi_pos])
    intro i hi
    exact partialCapAngle_eq_middle_of_mem_unused hα0 hα.le i (Or.inl hi)
  · apply sigma_Ioo_diff_singleton_eq_zero_of_halfplane_gap hV.imported_isConvexBody
      angle height hpoly hangle (by linarith [Real.pi_pos]) le_rfl (by linarith)
      (by linarith [Real.pi_pos])
    intro i hi
    exact partialCapAngle_eq_middle_of_mem_unused hα0 hα.le i (Or.inr hi)

/-- The unused curvature conclusion is derived from the actual maximizing
cap variation and its literal ceiling representation. -/
theorem IsJointCapMaximizer.upperCurvature_unused_except_middle_normal
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hα : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U (unusedNormalIntervals α \ {affineNormalAngle m}) = 0 :=
  upperCurvature_unused_of_usedSupportSaturation_capCut hU.isCap hU.angle_pos.le hα
    (hU.eq_usedSupportSaturation_capCut haffine)

end AmbidextrousSofa
