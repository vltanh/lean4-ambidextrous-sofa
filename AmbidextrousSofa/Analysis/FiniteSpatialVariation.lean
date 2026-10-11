module

public import AmbidextrousSofa.Analysis.ExposureMoments
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

/-!
# Spatial variation of literal finite wall expressions

A finite minimum/maximum of affine walls is globally Lipschitz. Away
from the finite set of ties, its spatial derivative is the selected
wall's slope. The absolutely continuous fundamental theorem therefore
identifies slope integrals with endpoint differences. In particular,
the two-sided height at any interior point is bounded by the integral
of the absolute selected slopes, with no interpretation of a limiting
source measure as graph arclength.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace WallExpr

variable {ι : Type*}

def affineGraph (e : WallExpr ι) (a b : ι → ℝ) (x : ℝ) : ℝ :=
  e.eval (fun i => a i * x + b i)

theorem continuous_affineGraph (e : WallExpr ι) (a b : ι → ℝ) :
    Continuous (e.affineGraph a b) :=
  e.continuous_eval (fun _ => by fun_prop)

theorem hasDerivAt_affineGraph (e : WallExpr ι) (a b : ι → ℝ) (x : ℝ)
    (hinj : Function.Injective (fun i => a i * x + b i)) :
    HasDerivAt (e.affineGraph a b) (e.sourceDensity a b a x) x := by
  have hd := e.hasDerivAt_affineEnvelope a b a x hinj
  rw [← sub_self x] at hd
  convert hd.comp_sub_const x x using 1
  exact funext fun y => congrArg e.eval (funext fun i => by ring)

theorem absolutelyContinuousOnInterval_affineGraph [Fintype ι]
    (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) :
    AbsolutelyContinuousOnInterval (e.affineGraph a b) l r := by
  refine (e.lipschitz_eval (K := ∑ i, ‖a i‖₊) fun i => LipschitzWith.of_dist_le_mul fun x y => ?_
    ).lipschitzOnWith.absolutelyContinuousOnInterval
  simp only [Real.dist_eq, NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, add_sub_add_right_eq_sub,
    ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j => |a j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)

theorem integral_sourceSlope [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ)
    (ha : Function.Injective a) (l r : ℝ) :
    (∫ x in l..r, e.sourceDensity a b a x) = e.affineGraph a b r - e.affineGraph a b l := by
  rw [← (e.absolutelyContinuousOnInterval_affineGraph a b l r).integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_injective_affine (b := b) ha] with x hx _
  exact (e.hasDerivAt_affineGraph a b x hx).deriv.symm

theorem peak_le_integral_abs_sourceSlope [Fintype ι]
    (e : WallExpr ι) (a b : ι → ℝ) (ha : Function.Injective a)
    {l x r : ℝ} (hlx : l ≤ x) (hxr : x ≤ r) :
    2 * e.affineGraph a b x - e.affineGraph a b l - e.affineGraph a b r ≤
      ∫ y in l..r, e.sourceDensity a b (fun i => |a i|) y := by
  have habs {l r : ℝ} (hlr : l ≤ r) : |e.affineGraph a b r - e.affineGraph a b l| ≤
      ∫ x in l..r, e.sourceDensity a b (fun i => |a i|) x := by
    rw [← e.integral_sourceSlope a b ha l r]
    exact intervalIntegral.abs_integral_le_integral_abs hlr
  linarith [habs hlx, habs hxr, le_abs_self (e.affineGraph a b x - e.affineGraph a b l),
    neg_le_abs (e.affineGraph a b r - e.affineGraph a b x),
    intervalIntegral.integral_add_adjacent_intervals
      (e.intervalIntegrable_sourceDensity a b (fun i => |a i|) l x)
      (e.intervalIntegrable_sourceDensity a b (fun i => |a i|) x r)]

end WallExpr

end AmbidextrousSofa
