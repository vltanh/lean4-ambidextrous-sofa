import AmbidextrousSofa.Analysis.FiniteEnvelope

/-!
# Finite spatial first variations and moving-window pressures

The finite envelope theorem differentiates actual min/max wall integrals.
Here it gives the charged exterior-source minus middle-source first
variation, and hence its necessary inequality at a selected maximum.

The separate endpoint calculation retains the motion of both ends of the
middle-half window. Its pressures involve `roof + niche`; they reduce to
one half only at special geometric configurations. These analytic formulas
apply to an actual axis-wall variation only after its positive end face
has been shown to move the actual projection endpoint.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- An ordinary three-integral spatial score with the middle half determined
by the actual endpoints. -/
def intervalSpatialScore (roof niche : ℝ → ℝ) (l r : ℝ) : ℝ :=
  (∫ x in l..(l + (r - l) / 4), roof x) +
    (∫ x in (r - (r - l) / 4)..r, roof x) -
    ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), niche x

theorem intervalSpatialScore_eq_whole_sub_middle {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r : ℝ) :
    intervalSpatialScore roof niche l r = (∫ x in l..r, roof x) -
      ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), roof x + niche x := by
  have hfirst := intervalIntegral.integral_add_adjacent_intervals
    (hroof.intervalIntegrable l (l + (r - l) / 4))
    (hroof.intervalIntegrable (l + (r - l) / 4) (r - (r - l) / 4))
  have hsecond := intervalIntegral.integral_add_adjacent_intervals
    (hroof.intervalIntegrable l (r - (r - l) / 4))
    (hroof.intervalIntegrable (r - (r - l) / 4) r)
  rw [intervalIntegral.integral_add (hroof.intervalIntegrable _ _)
    (hniche.intervalIntegrable _ _)]
  unfold intervalSpatialScore
  linarith

theorem hasDerivAt_primitive_affine_endpoint {f : ℝ → ℝ} (hf : Continuous f)
    (x d : ℝ) :
    HasDerivAt (fun ε : ℝ => ∫ t in (0 : ℝ)..(x + ε * d), f t) (f x * d) 0 := by
  have hline : HasDerivAt (fun ε : ℝ => x + ε * d) d 0 := by
    simpa only [zero_add, one_mul] using
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).mul_const d)
  have hprimitive := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 (x + 0 * d))
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  simpa only [zero_mul, add_zero] using hprimitive.comp 0 hline

/-- The ordinary two-endpoint Leibniz rule is obtained from continuous
primitives; no derivative of a set indicator is used. -/
theorem hasDerivAt_integral_affine_endpoints {f : ℝ → ℝ} (hf : Continuous f)
    (l r lD rD : ℝ) :
    HasDerivAt (fun ε : ℝ => ∫ x in (l + ε * lD)..(r + ε * rD), f x)
      (f r * rD - f l * lD) 0 := by
  have heq : (fun ε : ℝ => ∫ x in (l + ε * lD)..(r + ε * rD), f x) =
      fun ε => (∫ x in (0 : ℝ)..(r + ε * rD), f x) -
        ∫ x in (0 : ℝ)..(l + ε * lD), f x := by
    funext ε
    exact (intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
  rw [heq]
  exact (hasDerivAt_primitive_affine_endpoint hf r rD).sub
    (hasDerivAt_primitive_affine_endpoint hf l lD)

theorem hasDerivAt_intervalSpatialScore_endpoints {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r lD rD : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche (l + ε * lD) (r + ε * rD))
      (roof r * rD - roof l * lD -
        (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) * (lD + 3 * rD) / 4 +
        (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) * (3 * lD + rD) / 4) 0 := by
  have hwhole := hasDerivAt_integral_affine_endpoints hroof l r lD rD
  have hmiddle := hasDerivAt_integral_affine_endpoints (hroof.add hniche)
    (l + (r - l) / 4) (r - (r - l) / 4) ((3 * lD + rD) / 4) ((lD + 3 * rD) / 4)
  have heq : (fun ε : ℝ => intervalSpatialScore roof niche (l + ε * lD) (r + ε * rD)) =
      fun ε => (∫ x in (l + ε * lD)..(r + ε * rD), roof x) -
        ∫ x in (l + (r - l) / 4 + ε * ((3 * lD + rD) / 4))..
          (r - (r - l) / 4 + ε * ((lD + 3 * rD) / 4)), roof x + niche x := by
    funext ε
    rw [intervalSpatialScore_eq_whole_sub_middle hroof hniche]
    congr 2 <;> ring
  rw [heq]
  convert hwhole.sub hmiddle using 1 <;> ring

/-- FE.6: moving the right endpoint moves the middle endpoints with speeds
one quarter and three quarters, respectively. -/
theorem hasDerivAt_intervalSpatialScore_right {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche l (r + ε))
      (roof r + (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) / 4 -
        3 * (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) / 4) 0 := by
  convert hasDerivAt_intervalSpatialScore_endpoints hroof hniche l r 0 1 using 1
  · funext ε
    simp only [mul_zero, add_zero, mul_one]
  · ring

/-- FE.7: an outward left endpoint has speed minus one. -/
theorem hasDerivAt_intervalSpatialScore_left {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche (l - ε) r)
      (roof l - 3 * (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) / 4 +
        (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) / 4) 0 := by
  convert hasDerivAt_intervalSpatialScore_endpoints hroof hniche l r (-1) 0 using 1
  · funext ε
    simp only [mul_neg_one, mul_zero, add_zero, sub_eq_add_neg]
  · ring

/-- A right-sided maximum gives the sign of a derivative without extending
the geometric admissible family to negative perturbations. -/
theorem hasDerivAt_nonpos_of_right_max {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [hmax, self_mem_nhdsWithin] with ε hε hε0
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hε0.le) (sub_nonpos.mpr hε)

/-- The finite spatial score is differentiated from its min/max expressions
on all three spatial windows, rather than from an assumed contact chart. -/
theorem hasDerivAt_finite_intervalSpatialScore {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ)
    (ha : Function.Injective a) (hc : Function.Injective c) (l r : ℝ) :
    HasDerivAt (fun ε => intervalSpatialScore
      (outer.affineEnvelope a b w ε) (inner.affineEnvelope c d v ε) l r)
      ((∫ x in l..(l + (r - l) / 4), outer.sourceDensity a b w x) +
        (∫ x in (r - (r - l) / 4)..r, outer.sourceDensity a b w x) -
        ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), inner.sourceDensity c d v x) 0 :=
  ((outer.hasDerivAt_integral_affineEnvelope a b w ha _ _).add
    (outer.hasDerivAt_integral_affineEnvelope a b w ha _ _)).sub
    (inner.hasDerivAt_integral_affineEnvelope c d v hc _ _)

/-- At a selected maximum, the charged outer exposure is bounded by the
middle exposure plus the actual penalty derivative. The statement follows
from the proved finite-envelope integral derivative, not an exposure
certificate. Polygon admissibility of the chosen perturbation is a
separate geometric step. -/
theorem finite_selected_exposure_inequality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ)
    (ha : Function.Injective a) (hc : Function.Injective c) (l r : ℝ)
    {penalty : ℝ → ℝ} {penaltyD : ℝ} (hpenalty : HasDerivAt penalty penaltyD 0)
    (hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore (outer.affineEnvelope a b w ε) (inner.affineEnvelope c d v ε) l r -
        penalty ε ≤
      intervalSpatialScore (outer.affineEnvelope a b w 0) (inner.affineEnvelope c d v 0) l r -
        penalty 0) :
    (∫ x in l..(l + (r - l) / 4), outer.sourceDensity a b w x) +
      (∫ x in (r - (r - l) / 4)..r, outer.sourceDensity a b w x) ≤
      (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), inner.sourceDensity c d v x) + penaltyD := by
  have hderiv := (hasDerivAt_finite_intervalSpatialScore outer inner a b w c d v ha hc l r).sub
    hpenalty
  have hsign := hasDerivAt_nonpos_of_right_max hderiv hmax
  linarith

end AmbidextrousSofa
