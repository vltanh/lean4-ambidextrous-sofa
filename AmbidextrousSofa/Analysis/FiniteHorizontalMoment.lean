module

public import AmbidextrousSofa.Analysis.FiniteSourceBalance

@[expose] public section

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
  cases e.source (fun i => a i * x + b i) <;> simp [ite_le_one, ite_nonneg]

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
  simp [horizontalSourceDensity, e.integral_sourceDensity_eq_sum a b _ hlr, Fintype.sum_option]

/-- The floor is the only affine leaf that can vanish on a set of
positive measure, so the nonfloor sources fill exactly the region where the
expression is positive. No pointwise convention at the finitely many ties is
needed for the physical length identity. -/
theorem sum_nonfloor_sourceMass_eq_positive_measure [Fintype ι]
    (e : WallExpr (Option ι)) (a b : Option ι → ℝ)
    (ha : Function.Injective a) (ha0 : a none = 0) (hb0 : b none = 0)
    (he : ∀ x, 0 ≤ e.eval (fun i => a i * x + b i))
    {l r : ℝ} (hlr : l ≤ r) :
    (∑ j : ι, e.sourceMass a b l r (some j)) =
      volume.real (Ioc l r ∩ {x : ℝ | 0 < e.eval (fun i => a i * x + b i)}) := by
  have hae : e.sourceDensity a b horizontalSourceWeight =ᵐ[volume]
      {x : ℝ | 0 < e.eval (fun i => a i * x + b i)}.indicator (fun _ => 1) := by
    filter_upwards [ae_injective_affine (b := b) ha] with x hx
    have hvalue := e.eval_eq_source (fun i => a i * x + b i)
    rcases hsource : e.source (fun i => a i * x + b i) with _ | j <;>
      simp only [hsource, ha0, hb0, zero_mul, zero_add] at hvalue
    · simp [sourceDensity, hsource, horizontalSourceWeight, hvalue]
    · simp [sourceDensity, hsource, horizontalSourceWeight, (he x).lt_of_ne' fun hz =>
        Option.some_ne_none j (hx (by simpa [ha0, hb0, hz] using hvalue.symm))]
  have h := e.integral_sourceDensity_eq_sum a b horizontalSourceWeight hlr
  simp only [Fintype.sum_option, horizontalSourceWeight, mul_zero, zero_add, mul_one] at h
  rw [← h, intervalIntegral.integral_congr_ae (hae.mono fun x hx _ => hx),
    intervalIntegral.integral_of_le hlr, setIntegral_indicator (measurableSet_lt measurable_const
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
  rw [finitePositiveLength_eq_sum U normal corners terminal hslope (by unfold capWidth; linarith)]
  have hL := (roofExpr (ι := ι)).sum_sourceMass (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i)))
    (show horizontalLeft U ≤ horizontalLeft U + capWidth U / 4 by unfold capWidth; linarith)
  have hR := (roofExpr (ι := ι)).sum_sourceMass (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i)))
    (show horizontalRight U - capWidth U / 4 ≤ horizontalRight U by unfold capWidth; linarith)
  simp only [Fintype.sum_option, finiteExposureDefect, finiteWingMass, capWidth,
    Finset.sum_sub_distrib] at hL hR ⊢
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
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  unfold capWidth innerSourceMass innerDensity
  rw [finitePositiveLength_eq_sum _ _ _ _ (wallSlopes_injective grid) (by linarith)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_sourceDensity_outward _ _ _ _ (by linarith)]
  exact mul_div_cancel₀ _ (normal_snd_pos grid j).ne'

theorem sum_sin_normalizedExposureDefect_eq_horizontal_balance {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex grid, (normal grid j).2 * normalizedExposureDefect U grid j) =
      finitePositiveLength U (normal grid) (pairList grid) none
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) -
      (capWidth U / 2 - finiteWingMass U (normal grid) none) := by
  rw [← finite_horizontal_source_balance hU _ _ _ (wallSlopes_injective grid)]
  exact Finset.sum_congr rfl fun j _ => mul_div_cancel₀ _ (normal_snd_pos grid j).ne'

end AngularGrid

end AmbidextrousSofa
