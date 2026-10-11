module

public import AmbidextrousSofa.Analysis.FiniteHorizontalMoment
public import AmbidextrousSofa.Analysis.SourceOccupation

@[expose] public section

/-!
# Literal finite graph flux on spatial subintervals

The horizontal and vertical graph increments are exact weighted sums
of the selected affine sources. Projecting onto a fixed direction
preserves the separate first- and second-wall lengths. The local masses
below are integrals of the actual finite source densities, and their
comparison with the whole middle window uses only nonnegativity and
disjoint spatial intervals.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace WallExpr

variable {ι : Type*}

theorem sourceMass_eq_zero_of_no_source (e : WallExpr ι) (a b : ι → ℝ)
    (j : ι) {l r : ℝ}
    (hsource : ∀ x ∈ Ioc l r, e.source (fun i => a i * x + b i) ≠ j) :
    e.sourceMass a b l r j = 0 := by
  rw [sourceMass, show Ioc l r ∩ e.sourceSet a b j = ∅ from
    eq_empty_iff_forall_notMem.mpr fun x hx => hsource x hx.1 hx.2, measureReal_empty]

theorem graph_projection_eq_source_sum [Fintype ι]
    (e : WallExpr ι) (a b : ι → ℝ) (ha : Function.Injective a)
    {l r : ℝ} (hlr : l ≤ r) (c s : ℝ) :
    c * (r - l) + s * (e.affineGraph a b r - e.affineGraph a b l) =
      ∑ j, e.sourceMass a b l r j * (c + s * a j) := by
  rw [← e.sum_sourceMass a b hlr, ← e.integral_sourceSlope a b ha l r,
    e.integral_sourceDensity_eq_sum a b a hlr, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

end WallExpr

namespace AngularGrid

open FinitePolygon

def innerSourceMassOn (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) (j : SourceIndex grid) : ℝ :=
  ∫ x in l..r, innerDensity U grid j x

def innerAngularMassOn (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (l r : ℝ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
    innerSourceMassOn U grid l r j

theorem innerSourceMassOn_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) (j : SourceIndex grid) :
    0 ≤ innerSourceMassOn U grid l r j :=
  intervalIntegral.integral_nonneg_of_forall hlr (innerDensity_nonneg U grid j)

theorem innerSourceMassOn_eq_div (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) (j : SourceIndex grid) :
    innerSourceMassOn U grid l r j =
      (barrierExpr (pairList grid) none).sourceMass (wallSlope (normal grid))
        (barrierIntercept (normal grid) (fun i => support U (normal grid i))) l r (some j) /
          (normal grid j).2 := by
  classical
  exact integral_sourceDensity_outward _ _ _ _ hlr

theorem innerSourceMassOn_le (U : Set Plane) (grid : Finset QuarterAngle)
    {l r L R : ℝ} (hLl : L ≤ l) (hlr : l ≤ r) (hrR : r ≤ R) (j : SourceIndex grid) :
    innerSourceMassOn U grid l r j ≤ innerSourceMassOn U grid L R j :=
  intervalIntegral.integral_mono_interval hLl hlr hrR
    (Eventually.of_forall (innerDensity_nonneg U grid j))
    (intervalIntegrable_innerDensity U grid j L R)

theorem innerAngularMassOn_add_le (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) {L l₁ r₁ l₂ r₂ R : ℝ} (hL : L ≤ l₁) (h₁ : l₁ ≤ r₁)
    (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂) (hR : r₂ ≤ R) :
    innerAngularMassOn U grid E l₁ r₁ + innerAngularMassOn U grid E l₂ r₂ ≤
      innerAngularMassOn U grid E L R := by
  classical
  unfold innerAngularMassOn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ =>
    (add_le_add le_rfl (innerSourceMassOn_le U grid hgap h₂ le_rfl j)).trans ?_
  rw [innerSourceMassOn, innerSourceMassOn, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_innerDensity U grid j _ _) (intervalIntegrable_innerDensity U grid j _ _)]
  exact innerSourceMassOn_le U grid hL (h₁.trans (hgap.trans h₂)) hR j

theorem innerAngularMassOn_middle (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) :
    innerAngularMassOn U grid E
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) =
      innerAngularMass U grid E := rfl

theorem innerSourceMassOn_eq_zero_of_disjoint (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) (j : SourceIndex grid)
    (hsource : Ioc l r ∩ innerSourceSet U grid j = ∅) :
    innerSourceMassOn U grid l r j = 0 := by
  rw [innerSourceMassOn_eq_div U grid hlr]
  change volume.real (Ioc l r ∩ innerSourceSet U grid j) / _ = 0
  rw [hsource, measureReal_empty, zero_div]

/-- The baseline term is explicit before any positivity hypothesis.
Every nonfloor coefficient is the projection of that source's actual
unit graph tangent, and both source quarters remain separate. -/
theorem finiteBarrier_projection_eq_sources (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) (t : ℝ) :
    Real.cos t * (r - l) + Real.sin t *
        (finiteBarrier U (normal grid) (pairList grid) none r -
          finiteBarrier U (normal grid) (pairList grid) none l) =
      Real.cos t *
        (barrierExpr (pairList grid) none).sourceMass (wallSlope (normal grid))
          (barrierIntercept (normal grid) (fun i => support U (normal grid i))) l r none +
      ∑ j : SourceIndex grid, Real.sin (fullAngle grid j - t) * innerSourceMassOn U grid l r j := by
  classical
  rw [← affineGraph_barrier, (barrierExpr (pairList grid) none).graph_projection_eq_source_sum
    _ _ (wallSlopes_injective grid) hlr, Fintype.sum_option, wallSlope, mul_zero, add_zero,
    mul_comm]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  obtain ⟨hnx, hny⟩ : (normal grid j).1 = Real.cos (fullAngle grid j) ∧
    (normal grid j).2 = Real.sin (fullAngle grid j) := Prod.ext_iff.mp (normal_eq_unitNormal grid j)
  rw [innerSourceMassOn_eq_div U grid hlr, Real.sin_sub, wallSlope, ← hnx, ← hny]
  field_simp [(normal_snd_pos grid j).ne']
  ring

def finiteGraphProjection (U : Set Plane) (grid : Finset QuarterAngle)
    (t l r : ℝ) : ℝ :=
  Real.cos t * (r - l) + Real.sin t *
    (finiteBarrier U (normal grid) (pairList grid) none r -
      finiteBarrier U (normal grid) (pairList grid) none l)

/-- A localized first-family source has only its small transverse
projection; a second-family source contributes at most its full length.
The localization premise concerns actual selected source points. -/
theorem finiteGraphProjection_le_local_sources
    (U : Set Plane) (grid : Finset QuarterAngle) {l r t δ : ℝ}
    {E F : Set ℝ} (hlr : l ≤ r) (hδ : 0 ≤ δ)
    (hpos : ∀ x ∈ Ioc l r, 0 < finiteBarrier U (normal grid) (pairList grid) none x)
    (hlocal : ∀ x ∈ Ioc l r, ∀ j : SourceIndex grid, x ∈ innerSourceSet U grid j →
      fullAngle grid j ∈ E ∨
        (fullAngle grid j ∈ F ∧ Real.sin (fullAngle grid j - t) ≤ δ)) :
    finiteGraphProjection U grid t l r ≤
      innerAngularMassOn U grid E l r + δ * innerAngularMassOn U grid (E ∪ F) l r := by
  classical
  have hfloor : (barrierExpr (pairList grid) none).sourceMass (wallSlope (normal grid))
      (barrierIntercept (normal grid) (fun i => support U (normal grid i))) l r none = 0 := by
    refine WallExpr.sourceMass_eq_zero_of_no_source _ _ _ _ fun x hx heq => (hpos x hx).ne' ?_
    rw [finiteBarrier_eq_eval (normal grid) _ (fun _ => rfl), WallExpr.eval_eq_source, heq]
    simp [wallSlope, barrierIntercept]
  rw [finiteGraphProjection, finiteBarrier_projection_eq_sources U grid hlr t, hfloor, mul_zero,
    zero_add]
  simp only [innerAngularMassOn, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hm0 := innerSourceMassOn_nonneg U grid hlr j
  by_cases hm : innerSourceMassOn U grid l r j = 0
  · simp [hm]
  obtain ⟨x, hx, hsource⟩ := nonempty_iff_ne_empty.mpr
    (mt (innerSourceMassOn_eq_zero_of_disjoint U grid hlr j) hm)
  by_cases hE : fullAngle grid j ∈ E
  · simp only [hE, mem_union, true_or, ↓reduceIte]
    nlinarith [Real.sin_le_one (fullAngle grid j - t), mul_nonneg hδ hm0]
  · obtain ⟨hF, hsin⟩ := (hlocal x hx j hsource).resolve_left hE
    simp only [hE, hF, mem_union, or_true, ↓reduceIte, zero_add]
    exact mul_le_mul_of_nonneg_right hsin hm0

/-- The two spatial pieces are disjoint, so their second-family source
mass is charged only once to the full middle window. No limiting curve
length or smooth contact order occurs in this finite inequality. -/
theorem finiteGraphProjection_add_le_sources
    (U : Set Plane) (grid : Finset QuarterAngle) {L l₁ r₁ l₂ r₂ R t δ : ℝ}
    {E F : Set ℝ} (hL : L ≤ l₁) (h₁ : l₁ ≤ r₁) (hgap : r₁ ≤ l₂)
    (h₂ : l₂ ≤ r₂) (hR : r₂ ≤ R) (hδ : 0 ≤ δ)
    (hpos₁ : ∀ x ∈ Ioc l₁ r₁, 0 < finiteBarrier U (normal grid) (pairList grid) none x)
    (hpos₂ : ∀ x ∈ Ioc l₂ r₂, 0 < finiteBarrier U (normal grid) (pairList grid) none x)
    (hlocal₁ : ∀ x ∈ Ioc l₁ r₁, ∀ j : SourceIndex grid, x ∈ innerSourceSet U grid j →
      fullAngle grid j ∈ E ∨
        (fullAngle grid j ∈ F ∧ Real.sin (fullAngle grid j - t) ≤ δ))
    (hlocal₂ : ∀ x ∈ Ioc l₂ r₂, ∀ j : SourceIndex grid, x ∈ innerSourceSet U grid j →
      fullAngle grid j ∈ E ∨
        (fullAngle grid j ∈ F ∧ Real.sin (fullAngle grid j - t) ≤ δ)) :
    finiteGraphProjection U grid t l₁ r₁ + finiteGraphProjection U grid t l₂ r₂ ≤
      innerAngularMassOn U grid E L R + δ * innerAngularMassOn U grid (E ∪ F) L R := by
  have := finiteGraphProjection_le_local_sources U grid h₁ hδ hpos₁ hlocal₁
  have := finiteGraphProjection_le_local_sources U grid h₂ hδ hpos₂ hlocal₂
  have := innerAngularMassOn_add_le U grid E hL h₁ hgap h₂ hR
  have := mul_le_mul_of_nonneg_left
    (innerAngularMassOn_add_le U grid (E ∪ F) hL h₁ hgap h₂ hR) hδ
  linarith

end AngularGrid

end AmbidextrousSofa
