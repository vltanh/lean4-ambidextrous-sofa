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

theorem sourceDensity_eq_sum [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) (x : ℝ) :
    e.sourceDensity a b w x =
      ∑ j, (e.sourceSet a b j).indicator (fun _ => w j) x := by
  classical
  rw [Finset.sum_eq_single (e.source (fun i => a i * x + b i))]
  · simp [sourceDensity, sourceSet]
  · intro j _ hjs
    have hsj : e.source (fun i => a i * x + b i) ≠ j := Ne.symm hjs
    simp [sourceSet, hsj]
  · simp

theorem intervalIntegrable_sourceIndicator [DecidableEq ι] (e : WallExpr ι)
    (a b : ι → ℝ) (j : ι) (k l r : ℝ) :
    IntervalIntegrable ((e.sourceSet a b j).indicator (fun _ => k)) volume l r := by
  have hconstant : IntervalIntegrable (fun _ : ℝ => k) volume l r := intervalIntegrable_const
  exact ⟨hconstant.1.indicator (e.measurableSet_sourceSet a b j),
    hconstant.2.indicator (e.measurableSet_sourceSet a b j)⟩

theorem intervalIntegrable_sourceDensity [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) (l r : ℝ) :
    IntervalIntegrable (e.sourceDensity a b w) volume l r := by
  classical
  have heq : e.sourceDensity a b w =
      fun x => ∑ j, (e.sourceSet a b j).indicator (fun _ => w j) x :=
    funext (e.sourceDensity_eq_sum a b w)
  rw [heq]
  simpa only [Finset.sum_fn] using
    (IntervalIntegrable.sum Finset.univ (fun j _ =>
      e.intervalIntegrable_sourceIndicator a b j (w j) l r))

/-- The finite source partition integrates to ordinary physical horizontal
lengths, with no differentiability assertion built into those lengths. -/
theorem integral_sourceDensity_eq_sum [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, e.sourceDensity a b w x) =
      ∑ j, e.sourceMass a b l r j * w j := by
  classical
  have heq : e.sourceDensity a b w =
      fun x => ∑ j, (e.sourceSet a b j).indicator (fun _ => w j) x :=
    funext (e.sourceDensity_eq_sum a b w)
  rw [heq, intervalIntegral.integral_finsetSum (fun j _ =>
    e.intervalIntegrable_sourceIndicator a b j (w j) l r)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_of_le hlr,
    setIntegral_indicator (e.measurableSet_sourceSet a b j), setIntegral_const, smul_eq_mul]
  rfl

theorem sum_sourceMass [Fintype ι] (e : WallExpr ι)
    (a b : ι → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∑ j, e.sourceMass a b l r j) = r - l := by
  have h := e.integral_sourceDensity_eq_sum a b (fun _ => 1) hlr
  simpa only [sourceDensity, intervalIntegral.integral_const, smul_eq_mul, mul_one] using h.symm

theorem affineEnvelope_translation (e : WallExpr ι) (a b : ι → ℝ) (ε x : ℝ) :
    e.affineEnvelope a b (fun i => -a i) ε x =
      e.affineEnvelope a b (fun i => -a i) 0 (x - ε) := by
  unfold affineEnvelope
  congr 1
  funext i
  ring

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
  unfold finiteSourceVariation
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem finiteSourceVariation_neg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w : ι → ℝ) (v : κ → ℝ) :
    finiteSourceVariation outer inner a b c d l r (fun i => -w i) (fun j => -v j) =
      -finiteSourceVariation outer inner a b c d l r w v := by
  unfold finiteSourceVariation
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

theorem intervalSpatialScore_translate (roof niche : ℝ → ℝ) (l r ε : ℝ) :
    intervalSpatialScore (fun x => roof (x - ε)) (fun x => niche (x - ε))
        (l + ε) (r + ε) = intervalSpatialScore roof niche l r := by
  unfold intervalSpatialScore
  rw [intervalIntegral.integral_comp_sub_right,
    intervalIntegral.integral_comp_sub_right, intervalIntegral.integral_comp_sub_right]
  have hlow : l + ε + (r + ε - (l + ε)) / 4 - ε = l + (r - l) / 4 := by ring
  have hhigh : r + ε - (r + ε - (l + ε)) / 4 - ε = r - (r - l) / 4 := by ring
  simp only [add_sub_cancel_right, hlow, hhigh]

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
  have hderiv := hasDerivAt_finite_intervalSpatialScore_moving outer inner
    a b (fun i => -a i) c d (fun j => -c j) ha hc l r 1 1
  have hconstant : (fun ε => intervalSpatialScore
      (outer.affineEnvelope a b (fun i => -a i) ε)
      (inner.affineEnvelope c d (fun j => -c j) ε) (l + ε * 1) (r + ε * 1)) =
      fun _ : ℝ => intervalSpatialScore (outer.affineEnvelope a b (fun i => -a i) 0)
        (inner.affineEnvelope c d (fun j => -c j) 0) l r := by
    funext ε
    simp only [mul_one]
    have ho : outer.affineEnvelope a b (fun i => -a i) ε =
        fun x => outer.affineEnvelope a b (fun i => -a i) 0 (x - ε) :=
      funext (outer.affineEnvelope_translation a b ε)
    have hi : inner.affineEnvelope c d (fun j => -c j) ε =
        fun x => inner.affineEnvelope c d (fun j => -c j) 0 (x - ε) :=
      funext (inner.affineEnvelope_translation c d ε)
    rw [ho, hi, intervalSpatialScore_translate]
  rw [hconstant] at hderiv
  have hzero := hderiv.unique (hasDerivAt_const (0 : ℝ) _)
  rw [finiteSourceVariation_eq_integrals outer inner a b _ c d _ hlr]
  unfold rightEndpointPressure leftEndpointPressure
  linarith

end AmbidextrousSofa
