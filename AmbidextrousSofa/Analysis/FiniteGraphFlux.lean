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
  have hempty : Ioc l r ∩ e.sourceSet a b j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hsource x hx.1 hx.2
  simp only [sourceMass, hempty, Measure.real, measure_empty, ENNReal.toReal_zero]

theorem graph_projection_eq_source_sum [Fintype ι]
    (e : WallExpr ι) (a b : ι → ℝ) (ha : Function.Injective a)
    {l r : ℝ} (hlr : l ≤ r) (c s : ℝ) :
    c * (r - l) + s * (e.affineGraph a b r - e.affineGraph a b l) =
      ∑ j, e.sourceMass a b l r j * (c + s * a j) := by
  have hhorizontal := e.sum_sourceMass a b hlr
  have hvertical := e.integral_sourceSlope a b ha l r
  rw [e.integral_sourceDensity_eq_sum a b a hlr] at hvertical
  rw [← hhorizontal, ← hvertical]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

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
  unfold innerSourceMassOn innerDensity
  exact integral_sourceDensity_outward _ _ _ _ hlr

theorem innerSourceMassOn_le (U : Set Plane) (grid : Finset QuarterAngle)
    {l r L R : ℝ} (hLl : L ≤ l) (hlr : l ≤ r) (hrR : r ≤ R) (j : SourceIndex grid) :
    innerSourceMassOn U grid l r j ≤ innerSourceMassOn U grid L R j :=
  intervalIntegral.integral_mono_interval hLl hlr hrR
    (Eventually.of_forall (innerDensity_nonneg U grid j))
    (intervalIntegrable_innerDensity U grid j L R)

theorem innerSourceMassOn_add_le (U : Set Plane) (grid : Finset QuarterAngle)
    {L l₁ r₁ l₂ r₂ R : ℝ} (hL : L ≤ l₁) (h₁ : l₁ ≤ r₁)
    (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂) (hR : r₂ ≤ R) (j : SourceIndex grid) :
    innerSourceMassOn U grid l₁ r₁ j + innerSourceMassOn U grid l₂ r₂ j ≤
      innerSourceMassOn U grid L R j := by
  have hgap0 := innerSourceMassOn_nonneg U grid hgap j
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_innerDensity U grid j l₁ r₁)
    (intervalIntegrable_innerDensity U grid j r₁ l₂)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_innerDensity U grid j l₁ l₂)
    (intervalIntegrable_innerDensity U grid j l₂ r₂)
  have hwhole := innerSourceMassOn_le U grid hL (h₁.trans (hgap.trans h₂)) hR j
  dsimp only [innerSourceMassOn] at hgap0 hwhole ⊢
  linarith

theorem innerAngularMassOn_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) {l r : ℝ} (hlr : l ≤ r) :
    0 ≤ innerAngularMassOn U grid E l r := by
  classical
  exact Finset.sum_nonneg (fun j _ => innerSourceMassOn_nonneg U grid hlr j)

theorem innerAngularMassOn_le (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) {l r L R : ℝ} (hLl : L ≤ l) (hlr : l ≤ r) (hrR : r ≤ R) :
    innerAngularMassOn U grid E l r ≤ innerAngularMassOn U grid E L R := by
  classical
  exact Finset.sum_le_sum (fun j _ => innerSourceMassOn_le U grid hLl hlr hrR j)

theorem innerAngularMassOn_add_le (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) {L l₁ r₁ l₂ r₂ R : ℝ} (hL : L ≤ l₁) (h₁ : l₁ ≤ r₁)
    (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂) (hR : r₂ ≤ R) :
    innerAngularMassOn U grid E l₁ r₁ + innerAngularMassOn U grid E l₂ r₂ ≤
      innerAngularMassOn U grid E L R := by
  classical
  unfold innerAngularMassOn
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => innerSourceMassOn_add_le U grid hL h₁ hgap h₂ hR j)

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
  simp only [hsource, Measure.real, measure_empty, ENNReal.toReal_zero, zero_div]

theorem innerSourceMassOn_pos_has_source (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) (j : SourceIndex grid)
    (hpos : 0 < innerSourceMassOn U grid l r j) :
    ∃ x ∈ Ioc l r, x ∈ innerSourceSet U grid j := by
  by_contra hnot
  have hempty : Ioc l r ∩ innerSourceSet U grid j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hnot ⟨x, hx.1, hx.2⟩
  rw [innerSourceMassOn_eq_zero_of_disjoint U grid hlr j hempty] at hpos
  exact (lt_irrefl _ hpos)

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
  have h := (barrierExpr (pairList grid) none).graph_projection_eq_source_sum
    (wallSlope (normal grid))
    (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
    (wallSlopes_injective grid) hlr (Real.cos t) (Real.sin t)
  rw [affineGraph_barrier, Fintype.sum_option] at h
  rw [h]
  simp only [wallSlope, mul_zero, add_zero]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [innerSourceMassOn_eq_div U grid hlr, Real.sin_sub]
    have hn := normal_eq_unitNormal grid j
    have hnx : (normal grid j).1 = Real.cos (fullAngle grid j) := congrArg Prod.fst hn
    have hny : (normal grid j).2 = Real.sin (fullAngle grid j) := congrArg Prod.snd hn
    rw [← hnx, ← hny]
    field_simp [(normal_snd_pos grid j).ne']
    ring

theorem finiteBarrier_projection_eq_sources_of_positive
    (U : Set Plane) (grid : Finset QuarterAngle) {l r : ℝ} (hlr : l ≤ r) (t : ℝ)
    (hpos : ∀ x ∈ Ioc l r, 0 < finiteBarrier U (normal grid) (pairList grid) none x) :
    Real.cos t * (r - l) + Real.sin t *
        (finiteBarrier U (normal grid) (pairList grid) none r -
          finiteBarrier U (normal grid) (pairList grid) none l) =
      ∑ j : SourceIndex grid, Real.sin (fullAngle grid j - t) * innerSourceMassOn U grid l r j := by
  have hfloor : (barrierExpr (pairList grid) none).sourceMass (wallSlope (normal grid))
      (barrierIntercept (normal grid) (fun i => support U (normal grid i))) l r none = 0 := by
    apply WallExpr.sourceMass_eq_zero_of_no_source
    intro x hx heq
    have hvalue := (barrierExpr (pairList grid) none).eval_eq_source
      (fun i => wallSlope (normal grid) i * x +
        barrierIntercept (normal grid) (fun j => support U (normal grid j)) i)
    have hz : finiteBarrier U (normal grid) (pairList grid) none x = 0 := by
      rw [finiteBarrier_eq_eval (normal grid) _ (fun _ => rfl)]
      rw [heq] at hvalue
      simpa only [wallSlope, barrierIntercept, zero_mul, zero_add] using hvalue
    exact (ne_of_gt (hpos x hx)) hz
  simpa only [hfloor, mul_zero, zero_add] using finiteBarrier_projection_eq_sources U grid hlr t

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
  unfold finiteGraphProjection
  rw [finiteBarrier_projection_eq_sources_of_positive U grid hlr t hpos]
  simp only [innerAngularMassOn, Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hm0 := innerSourceMassOn_nonneg U grid hlr j
  by_cases hm : innerSourceMassOn U grid l r j = 0
  · simp only [hm, mul_zero, ite_self, add_zero, le_refl]
  · have hmpos : 0 < innerSourceMassOn U grid l r j := lt_of_le_of_ne hm0 (Ne.symm hm)
    obtain ⟨x, hx, hsource⟩ := innerSourceMassOn_pos_has_source U grid hlr j hmpos
    by_cases hE : fullAngle grid j ∈ E
    · have hEF : fullAngle grid j ∈ E ∪ F := Or.inl hE
      simp only [if_pos hE, if_pos hEF]
      have hproj := mul_le_mul_of_nonneg_right (Real.sin_le_one (fullAngle grid j - t)) hm0
      have herr := mul_nonneg hδ hm0
      linarith
    · have hF := (hlocal x hx j hsource).resolve_left hE
      have hEF : fullAngle grid j ∈ E ∪ F := Or.inr hF.1
      simp only [if_neg hE, if_pos hEF, zero_add]
      exact mul_le_mul_of_nonneg_right hF.2 hm0

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
  have hfirst := finiteGraphProjection_le_local_sources U grid h₁ hδ hpos₁ hlocal₁
  have hsecond := finiteGraphProjection_le_local_sources U grid h₂ hδ hpos₂ hlocal₂
  have hmass := innerAngularMassOn_add_le U grid E hL h₁ hgap h₂ hR
  have herr := mul_le_mul_of_nonneg_left
    (innerAngularMassOn_add_le U grid (E ∪ F) hL h₁ hgap h₂ hR) hδ
  nlinarith

end AngularGrid

end AmbidextrousSofa
