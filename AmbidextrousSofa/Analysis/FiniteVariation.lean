module

public import AmbidextrousSofa.Analysis.FiniteEnvelope

@[expose] public section

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

/-- The ordinary two-endpoint Leibniz rule is obtained from continuous
primitives; no derivative of a set indicator is used. -/
theorem hasDerivAt_integral_affine_endpoints {f : ℝ → ℝ} (hf : Continuous f)
    (l r lD rD : ℝ) :
    HasDerivAt (fun ε : ℝ => ∫ x in (l + ε * lD)..(r + ε * rD), f x)
      (f r * rD - f l * lD) 0 := by
  have hP (x d : ℝ) : HasDerivAt (fun ε : ℝ => ∫ t in (0 : ℝ)..(x + ε * d), f t) (f x * d) 0 := by
    simpa only [zero_mul, add_zero, Function.comp_def] using
      (hf.integral_hasStrictDerivAt 0 (x + 0 * d)).hasDerivAt.comp 0
        ((hasDerivAt_mul_const d).const_add x)
  exact ((hP r rD).sub (hP l lD)).congr_of_eventuallyEq (Eventually.of_forall fun ε =>
    (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm)

theorem hasDerivAt_intervalSpatialScore_endpoints {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r lD rD : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche (l + ε * lD) (r + ε * rD))
      (roof r * rD - roof l * lD -
        (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) * (lD + 3 * rD) / 4 +
        (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) * (3 * lD + rD) / 4) 0 := by
  convert ((hasDerivAt_integral_affine_endpoints hroof l (l + (r - l) / 4) lD
    ((3 * lD + rD) / 4)).add (hasDerivAt_integral_affine_endpoints hroof (r - (r - l) / 4) r
    ((lD + 3 * rD) / 4) rD)).sub (hasDerivAt_integral_affine_endpoints hniche (l + (r - l) / 4)
    (r - (r - l) / 4) ((3 * lD + rD) / 4) ((lD + 3 * rD) / 4)) using 1
  · funext ε
    unfold intervalSpatialScore
    congr 1
    · congr 1 <;> congr 1 <;> ring
    · congr 1 <;> ring
  · ring

/-- FE.6: moving the right endpoint moves the middle endpoints with speeds
one quarter and three quarters, respectively. -/
theorem hasDerivAt_intervalSpatialScore_right {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche l (r + ε))
      (roof r + (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) / 4 -
        3 * (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) / 4) 0 := by
  convert hasDerivAt_intervalSpatialScore_endpoints hroof hniche l r 0 1 using 1
  · simp only [mul_zero, add_zero, mul_one]
  · ring

/-- FE.7: an outward left endpoint has speed minus one. -/
theorem hasDerivAt_intervalSpatialScore_left {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche (l - ε) r)
      (roof l - 3 * (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) / 4 +
        (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) / 4) 0 := by
  convert hasDerivAt_intervalSpatialScore_endpoints hroof hniche l r (-1) 0 using 1
  · simp only [mul_neg_one, mul_zero, add_zero, sub_eq_add_neg]
  · ring

/-- A right-sided maximum gives the sign of a derivative without extending
the geometric admissible family to negative perturbations. -/
theorem hasDerivAt_nonpos_of_right_max {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [hmax, self_mem_nhdsWithin] with ε hε hε0
  simpa using mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hε0.le) (sub_nonpos.mpr hε)

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
  have hderiv : HasDerivAt (fun ε => intervalSpatialScore (outer.affineEnvelope a b w ε)
      (inner.affineEnvelope c d v ε) l r - penalty ε) (_ - penaltyD) 0 :=
    (((outer.hasDerivAt_integral_affineEnvelope a b w ha _ _).add
      (outer.hasDerivAt_integral_affineEnvelope a b w ha _ _)).sub
      (inner.hasDerivAt_integral_affineEnvelope c d v hc _ _)).sub hpenalty
  linarith [hasDerivAt_nonpos_of_right_max hderiv hmax]

end AmbidextrousSofa
