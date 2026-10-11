module

public import AmbidextrousSofa.Analysis.ErosionVariation

@[expose] public section

/-!
# Literal source masses and the translation balance

Every mass in this file is the Lebesgue measure of the actual selected
source set of a finite min/max expression. Integrating all wall velocities
gives a finite weighted sum of these masses. Horizontal translation then
gives the exact signed endpoint balance. No limiting niche graph or
identification of a weak limit with graph arclength is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace WallExpr

variable {ι : Type*}

def sourceMass (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) (j : ι) : ℝ :=
  volume.real (Ioc l r ∩ e.sourceSet a b j)

theorem sourceMass_nonneg (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) (j : ι) :
    0 ≤ e.sourceMass a b l r j := ENNReal.toReal_nonneg

theorem intervalIntegrable_sourceDensity [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) (l r : ℝ) :
    IntervalIntegrable (e.sourceDensity a b w) volume l r :=
  intervalIntegrable_const.mono_fun' (e.measurable_sourceDensity a b w).aestronglyMeasurable
    (.of_forall fun _ => Finset.single_le_sum (f := fun i => |w i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ _))

/-- The finite source partition integrates to ordinary physical horizontal
lengths, with no differentiability assertion built into those lengths. -/
theorem integral_sourceDensity_eq_sum [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, e.sourceDensity a b w x) =
      ∑ j, e.sourceMass a b l r j * w j := by
  classical
  have hsum x : e.sourceDensity a b w x = ∑ j, (e.sourceSet a b j).indicator (fun _ => w j) x := by
    simp [sourceDensity, sourceSet, indicator_apply]
  simp_rw [intervalIntegral.integral_of_le hlr, hsum]
  rw [integral_finsetSum _ fun j _ => ((integrableOn_const measure_Ioc_lt_top.ne).indicator
    (e.measurableSet_sourceSet a b j)).integrable]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [setIntegral_indicator (e.measurableSet_sourceSet a b j), setIntegral_const, smul_eq_mul]
  rfl

theorem sum_sourceMass [Fintype ι] (e : WallExpr ι)
    (a b : ι → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∑ j, e.sourceMass a b l r j) = r - l := by
  simpa [sourceDensity] using (e.integral_sourceDensity_eq_sum a b (fun _ => 1) hlr).symm

end WallExpr

/-- Total wall variation, using the two charged exterior source masses
and the central source masses. The two expressions can have different
finite source types. -/
def finiteSourceVariation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w : ι → ℝ) (v : κ → ℝ) : ℝ :=
  (∑ i, (outer.sourceMass a b l (l + (r - l) / 4) i +
    outer.sourceMass a b (r - (r - l) / 4) r i) * w i) -
      ∑ j, inner.sourceMass c d (l + (r - l) / 4) (r - (r - l) / 4) j * v j

theorem finiteSourceVariation_eq_integrals {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ)
    {l r : ℝ} (hlr : l ≤ r) :
    finiteSourceVariation outer inner a b c d l r w v =
      (∫ x in l..(l + (r - l) / 4), outer.sourceDensity a b w x) +
        (∫ x in (r - (r - l) / 4)..r, outer.sourceDensity a b w x) -
        ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), inner.sourceDensity c d v x := by
  rw [outer.integral_sourceDensity_eq_sum a b w (by linarith),
    outer.integral_sourceDensity_eq_sum a b w (by linarith),
    inner.integral_sourceDensity_eq_sum c d v (by linarith)]
  simp only [finiteSourceVariation, add_mul, Finset.sum_add_distrib]

theorem finiteSourceVariation_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w w' : ι → ℝ) (v v' : κ → ℝ) :
    finiteSourceVariation outer inner a b c d l r (fun i => w i + w' i)
        (fun j => v j + v' j) =
      finiteSourceVariation outer inner a b c d l r w v +
        finiteSourceVariation outer inner a b c d l r w' v' := by
  simp only [finiteSourceVariation, mul_add, Finset.sum_add_distrib]
  ring

theorem finiteSourceVariation_neg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w : ι → ℝ) (v : κ → ℝ) :
    finiteSourceVariation outer inner a b c d l r (fun i => -w i) (fun j => -v j) =
      -finiteSourceVariation outer inner a b c d l r w v := by
  simp only [finiteSourceVariation, mul_neg, Finset.sum_neg_distrib]
  ring

theorem intervalSpatialScore_translate (roof niche : ℝ → ℝ) (l r ε : ℝ) :
    intervalSpatialScore (fun x => roof (x - ε)) (fun x => niche (x - ε))
        (l + ε) (r + ε) = intervalSpatialScore roof niche l r := by
  simp only [intervalSpatialScore, intervalIntegral.integral_comp_sub_right]
  ring_nf

/-- Exact total translation balance for finite physical source measures.
The endpoint terms include the motion of the central half-window. -/
theorem finiteSourceVariation_translation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (ha : Function.Injective a) (hc : Function.Injective c)
    {l r : ℝ} (hlr : l ≤ r) :
    finiteSourceVariation outer inner a b c d l r (fun i => -a i) (fun j => -c j) =
      outer.affineEnvelope a b (fun i => -a i) 0 l -
        outer.affineEnvelope a b (fun i => -a i) 0 r +
        rightEndpointPressure (outer.affineEnvelope a b (fun i => -a i) 0)
          (inner.affineEnvelope c d (fun j => -c j) 0) l r -
        leftEndpointPressure (outer.affineEnvelope a b (fun i => -a i) 0)
          (inner.affineEnvelope c d (fun j => -c j) 0) l r := by
  have hconstant (ε : ℝ) : intervalSpatialScore (outer.affineEnvelope a b (fun i => -a i) ε)
      (inner.affineEnvelope c d (fun j => -c j) ε) (l + ε * 1) (r + ε * 1) =
      intervalSpatialScore (outer.affineEnvelope a b (fun i => -a i) 0)
        (inner.affineEnvelope c d (fun j => -c j) 0) l r := by
    rw [← intervalSpatialScore_translate _ _ l r ε, mul_one]
    congr 1 <;> funext x <;> simp only [WallExpr.affineEnvelope] <;> congr 1 <;> funext i <;> ring
  have hzero := (hasDerivAt_finite_intervalSpatialScore_moving outer inner a b (fun i => -a i)
    c d (fun j => -c j) ha hc l r 1 1).unique
    ((hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq (.of_forall hconstant))
  rw [finiteSourceVariation_eq_integrals outer inner a b _ c d _ hlr]
  unfold rightEndpointPressure leftEndpointPressure
  linarith

end AmbidextrousSofa
