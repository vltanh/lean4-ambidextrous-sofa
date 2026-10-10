module

public import MovingSofaOptimality.Basic.SurfaceArea
public import AmbidextrousSofa.Analysis.CapCompactness

@[expose] public section

/-!
# Actual support curvature and the imported convex-body calculus

The imported surface-area measure is constructed from the actual supporting
faces of the set. The identities below identify its support function with
the coordinate support already used by the cap objective. Product-metric
Hausdorff convergence implies the uniform angular-support convergence used
by that calculus. No maximization or curvature inequality is a premise of
this bridge.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem angleSupport_eq_imported_supp (U : Set Plane) (t : ℝ) :
    angleSupport U t = MovingSofaOptimality.supp U t := rfl

theorem IsDownwardCap.imported_isConvexBody {U : Set Plane}
    (hU : IsDownwardCap U) : MovingSofaOptimality.IsConvexBody U :=
  ⟨hU.nonempty, hU.isCompact, hU.convex⟩

theorem imported_hausdorffDist_le_two_mul {U V : Set Plane}
    (hU : IsCompact U) (hUne : U.Nonempty)
    (hV : IsCompact V) (hVne : V.Nonempty) :
    MovingSofaOptimality.hausdorffDist U V ≤ 2 * Metric.hausdorffDist U V := by
  apply ciSup_le
  intro t
  change |support U (unitNormal t) - support V (unitNormal t)| ≤ _
  calc
    |support U (unitNormal t) - support V (unitNormal t)| ≤
        Metric.hausdorffDist U V *
          (|(unitNormal t).1| + |(unitNormal t).2|) :=
      abs_support_sub_le_hausdorff hU hUne hV hVne _
    _ ≤ Metric.hausdorffDist U V * 2 := by
      apply mul_le_mul_of_nonneg_left _ Metric.hausdorffDist_nonneg
      change |Real.cos t| + |Real.sin t| ≤ 2
      linarith [Real.abs_cos_le_one t, Real.abs_sin_le_one t]
    _ = 2 * Metric.hausdorffDist U V := mul_comm _ _

theorem CapHausdorffTendsto.imported_hausdorffTendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    MovingSofaOptimality.HausdorffTendsto U K := by
  apply squeeze_zero (fun n => MovingSofaOptimality.hausdorffDist_nonneg (U n) K)
    (fun n => imported_hausdorffDist_le_two_mul
      (hU n).isCompact (hU n).nonempty hK.isCompact hK.nonempty)
  simpa only [mul_zero] using h.const_mul 2

/-- The periodic angular curvature measure of the actual supporting faces. -/
def upperCurvature (U : Set Plane) : Measure ℝ := MovingSofaOptimality.sigma U

instance upperCurvature_isLocallyFiniteMeasure (U : Set Plane) :
    IsLocallyFiniteMeasure (upperCurvature U) :=
  inferInstanceAs (IsLocallyFiniteMeasure (MovingSofaOptimality.sigma U))

theorem IsDownwardCap.upperCurvature_Ioc {U : Set Plane}
    (hU : IsDownwardCap U) (a b : ℝ) :
    upperCurvature U (Ioc a b) =
      ENNReal.ofReal (MovingSofaOptimality.sigmaFun U b - MovingSofaOptimality.sigmaFun U a) :=
  MovingSofaOptimality.sigma_Ioc hU.imported_isConvexBody a b

theorem IsDownwardCap.angleSupport_right_deriv {U : Set Plane}
    (hU : IsDownwardCap U) (t : ℝ) :
    HasDerivWithinAt (angleSupport U)
      (coordDot (MovingSofaOptimality.vplus U t) (MovingSofaOptimality.vvec t)) (Ici t) t :=
  MovingSofaOptimality.hasDerivWithinAt_supp_right hU.imported_isConvexBody t

theorem IsDownwardCap.angleSupport_left_deriv {U : Set Plane}
    (hU : IsDownwardCap U) (t : ℝ) :
    HasDerivWithinAt (angleSupport U)
      (coordDot (MovingSofaOptimality.vminus U t) (MovingSofaOptimality.vvec t)) (Iic t) t :=
  MovingSofaOptimality.hasDerivWithinAt_supp_left hU.imported_isConvexBody t

end AmbidextrousSofa
