import AmbidextrousSofa.Analysis.FiniteSourceBalance

/-!
# The literal finite horizontal source moment

Every selected nonfloor leaf contributes one unit of horizontal density.
Distinct affine slopes make a nonfloor leaf equal to the floor only on a
null set. Consequently the sum of its actual physical source lengths is
exactly the measure of the region where the finite barrier is positive.
The formula includes the whole proper-terminal source and historical ties.

The normalized support derivative has density `1 / sin θ`; multiplication
by the vertical normal component recovers this physical horizontal length.
The final identity retains the horizontal top leaf of the outer roof and
both charged exterior intervals explicitly.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace WallExpr

variable {ι : Type*}

def horizontalSourceWeight : Option ι → ℝ
  | none => 0
  | some _ => 1

/-- A selected collection of nonfloor sources has multiplicity at most
one, including at every tie of the finite min/max expression. -/
def horizontalSourceDensity [DecidableEq ι] (e : WallExpr (Option ι))
    (a b : Option ι → ℝ) (F : Finset ι) (x : ℝ) : ℝ :=
  e.sourceDensity a b (fun i => match i with
    | none => 0
    | some j => if j ∈ F then 1 else 0) x

theorem horizontalSourceDensity_bounds [DecidableEq ι] (e : WallExpr (Option ι))
    (a b : Option ι → ℝ) (F : Finset ι) (x : ℝ) :
    0 ≤ e.horizontalSourceDensity a b F x ∧
      e.horizontalSourceDensity a b F x ≤ 1 := by
  unfold horizontalSourceDensity sourceDensity
  cases e.source (fun i => a i * x + b i) with
  | none => norm_num
  | some j => by_cases hj : j ∈ F <;> simp [hj]

theorem measurable_horizontalSourceDensity [DecidableEq ι]
    (e : WallExpr (Option ι)) (a b : Option ι → ℝ) (F : Finset ι) :
    Measurable (e.horizontalSourceDensity a b F) :=
  e.measurable_sourceDensity a b _

theorem intervalIntegrable_horizontalSourceDensity [Fintype ι] [DecidableEq ι]
    (e : WallExpr (Option ι)) (a b : Option ι → ℝ) (F : Finset ι) (l r : ℝ) :
    IntervalIntegrable (e.horizontalSourceDensity a b F) volume l r :=
  e.intervalIntegrable_sourceDensity a b _ l r

theorem integral_horizontalSourceDensity [Fintype ι] [DecidableEq ι]
    (e : WallExpr (Option ι)) (a b : Option ι → ℝ) (F : Finset ι)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, e.horizontalSourceDensity a b F x) =
      ∑ j ∈ F, e.sourceMass a b l r (some j) := by
  rw [horizontalSourceDensity, e.integral_sourceDensity_eq_sum a b _ hlr]
  simp only [Fintype.sum_option, mul_zero, zero_add]
  simp

theorem horizontalSourceDensity_univ [Fintype ι] [DecidableEq ι]
    (e : WallExpr (Option ι)) (a b : Option ι → ℝ) :
    e.horizontalSourceDensity a b Finset.univ =
      e.sourceDensity a b horizontalSourceWeight := by
  funext x
  unfold horizontalSourceDensity sourceDensity
  cases e.source (fun i => a i * x + b i) <;> simp [horizontalSourceWeight]

/-- The floor is the only affine leaf that can vanish on a set of
positive measure. No pointwise convention at the finitely many ties is
needed for the physical length identity. -/
theorem horizontalSourceDensity_ae_eq_positive [Fintype ι]
    (e : WallExpr (Option ι)) (a b : Option ι → ℝ)
    (ha : Function.Injective a) (ha0 : a none = 0) (hb0 : b none = 0)
    (he : ∀ x, 0 ≤ e.eval (fun i => a i * x + b i)) :
    e.sourceDensity a b horizontalSourceWeight =ᵐ[volume]
      {x : ℝ | 0 < e.eval (fun i => a i * x + b i)}.indicator (fun _ => 1) := by
  classical
  filter_upwards [ae_injective_affine (b := b) ha] with x hx
  have hvalue := e.eval_eq_source (fun i => a i * x + b i)
  cases hsource : e.source (fun i => a i * x + b i) with
  | none =>
    have hz : e.eval (fun i => a i * x + b i) = 0 := by
      simpa only [hsource, ha0, hb0, zero_mul, zero_add] using hvalue
    simp [sourceDensity, hsource, horizontalSourceWeight, hz]
  | some j =>
    have hne : e.eval (fun i => a i * x + b i) ≠ 0 := by
      intro hz
      have heq : a (some j) * x + b (some j) = a none * x + b none := by
        simpa only [hsource, ha0, hb0, zero_mul, zero_add, hz] using hvalue.symm
      exact Option.noConfusion (hx heq)
    have hpos : 0 < e.eval (fun i => a i * x + b i) :=
      lt_of_le_of_ne (he x) (Ne.symm hne)
    simp [sourceDensity, hsource, horizontalSourceWeight, hpos]

theorem sum_nonfloor_sourceMass_eq_positive_measure [Fintype ι]
    (e : WallExpr (Option ι)) (a b : Option ι → ℝ)
    (ha : Function.Injective a) (ha0 : a none = 0) (hb0 : b none = 0)
    (he : ∀ x, 0 ≤ e.eval (fun i => a i * x + b i))
    {l r : ℝ} (hlr : l ≤ r) :
    (∑ j : ι, e.sourceMass a b l r (some j)) =
      volume.real (Ioc l r ∩ {x : ℝ | 0 < e.eval (fun i => a i * x + b i)}) := by
  classical
  have h := e.integral_sourceDensity_eq_sum a b horizontalSourceWeight hlr
  simp only [Fintype.sum_option, horizontalSourceWeight, mul_zero, zero_add, mul_one] at h
  rw [← h, intervalIntegral.integral_congr_ae (by
    filter_upwards [e.horizontalSourceDensity_ae_eq_positive a b ha ha0 hb0 he]
      with x hx _ using hx)]
  rw [intervalIntegral.integral_of_le hlr,
    setIntegral_indicator (measurableSet_lt measurable_const
      (e.continuous_eval (fun _ => by fun_prop)).measurable),
    setIntegral_const, smul_eq_mul, mul_one]

end WallExpr

namespace FinitePolygon

variable {ι : Type*}

def finitePositiveLength (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (l r : ℝ) : ℝ :=
  volume.real (Ioc l r ∩ {x : ℝ | 0 < finiteBarrier U normal corners terminal x})

theorem finitePositiveLength_eq_sum [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι)
    (hslope : Function.Injective (wallSlope normal)) {l r : ℝ} (hlr : l ≤ r) :
    finitePositiveLength U normal corners terminal l r =
      ∑ j : ι, (barrierExpr corners terminal).sourceMass (wallSlope normal)
        (barrierIntercept normal (fun i => support U (normal i))) l r (some j) := by
  have heq (x : ℝ) := finiteBarrier_eq_eval normal
    (fun i => support U (normal i)) (fun _ => rfl) corners terminal x
  have h := (barrierExpr corners terminal).sum_nonfloor_sourceMass_eq_positive_measure
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    hslope rfl rfl (fun x => by rw [← heq]; exact finiteBarrier_nonneg _ _ _ _ _) hlr
  simpa only [finitePositiveLength, ← heq] using h.symm

theorem sum_finiteWingMass [Fintype ι] {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) :
    (∑ i : Option ι, finiteWingMass U normal i) = capWidth U / 2 := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hL := (roofExpr (ι := ι)).sum_sourceMass (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i)))
    (show horizontalLeft U ≤ horizontalLeft U +
      (horizontalRight U - horizontalLeft U) / 4 by linarith)
  have hR := (roofExpr (ι := ι)).sum_sourceMass (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i)))
    (show horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U by linarith)
  simp only [finiteWingMass, Finset.sum_add_distrib]
  rw [hL, hR]
  unfold capWidth
  ring

/-- Exact physical horizontal balance, with the top leaf and both moving
exterior intervals retained. This holds for arbitrary paired corners and
for a whole proper-terminal first wall. -/
theorem finite_horizontal_source_balance [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι)
    (hslope : Function.Injective (wallSlope normal)) :
    (∑ j : ι, finiteExposureDefect U normal corners terminal j) =
      finitePositiveLength U normal corners terminal
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) -
      (capWidth U / 2 - finiteWingMass U normal none) := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hpos := finitePositiveLength_eq_sum U normal corners terminal hslope
    (show horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 by
      unfold capWidth; linarith)
  have houter := sum_finiteWingMass hU normal
  rw [Fintype.sum_option] at houter
  unfold finiteExposureDefect
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  change _ - _ - _ = _
  have hw : (∑ j : ι, finiteWingMass U normal (some j)) =
      (∑ j : ι, (roofExpr (ι := ι)).sourceMass (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) (some j)) +
      ∑ j : ι, (roofExpr (ι := ι)).sourceMass (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i)))
        (horizontalRight U - capWidth U / 4) (horizontalRight U) (some j) := by
    simp only [finiteWingMass, capWidth, Finset.sum_add_distrib]
  rw [hpos]
  change _ - _ - _ = _
  linarith

end FinitePolygon

namespace AngularGrid

open FinitePolygon

/-- The sine-weighted literal inner mass equals ordinary positive niche
length. In particular this is a horizontal measure, not an arclength
assigned to a limiting envelope. -/
theorem sum_sin_innerSourceMass_eq_positiveLength {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex grid, (normal grid j).2 * innerSourceMass U grid j) =
      finitePositiveLength U (normal grid) (pairList grid) none
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [finitePositiveLength_eq_sum _ _ _ _ (wallSlopes_injective grid) (by
    unfold capWidth; linarith)]
  apply Finset.sum_congr rfl
  intro j _
  unfold innerSourceMass innerDensity
  rw [integral_sourceDensity_outward _ _ _ _ (by linarith)]
  unfold WallExpr.sourceMass
  field_simp [(normal_snd_pos grid j).ne']

theorem sum_sin_normalizedExposureDefect_eq_horizontal_balance {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex grid, (normal grid j).2 * normalizedExposureDefect U grid j) =
      finitePositiveLength U (normal grid) (pairList grid) none
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) -
      (capWidth U / 2 - finiteWingMass U (normal grid) none) := by
  have hterm (j : SourceIndex grid) :
      (normal grid j).2 * normalizedExposureDefect U grid j =
        finiteExposureDefect U (normal grid) (pairList grid) none j := by
    unfold normalizedExposureDefect
    field_simp [(normal_snd_pos grid j).ne']
  simp only [hterm]
  exact finite_horizontal_source_balance hU _ _ _ (wallSlopes_injective grid)

end AngularGrid

end AmbidextrousSofa
