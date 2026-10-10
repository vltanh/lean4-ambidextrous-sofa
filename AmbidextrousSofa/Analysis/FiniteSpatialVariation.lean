import AmbidextrousSofa.Analysis.ExposureMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

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
  have hd' : HasDerivAt (fun ε => e.affineEnvelope a b a ε x)
      (e.sourceDensity a b a x) (x - x) := by
    simpa only [sub_self] using hd
  have h := hd'.comp x ((hasDerivAt_id x).sub_const x)
  convert h using 1
  · funext y
    unfold affineGraph affineEnvelope
    congr 1
    funext i
    ring
  · simp

theorem lipschitz_affineGraph [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ) :
    LipschitzWith (Real.nnabs (∑ i, |a i|)) (e.affineGraph a b) := by
  have hK : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg (a i))
  have hbound : ∀ i, |a i| ≤ ∑ j, |a j| := fun i =>
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  apply e.lipschitz_eval
  intro i
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hK]
  calc
    |a i * x + b i - (a i * y + b i)| = |a i| * |x - y| := by
      rw [show a i * x + b i - (a i * y + b i) = a i * (x - y) by ring, abs_mul]
    _ ≤ (∑ j, |a j|) * |x - y| :=
      mul_le_mul_of_nonneg_right (hbound i) (abs_nonneg _)

theorem absolutelyContinuousOnInterval_affineGraph [Fintype ι]
    (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) :
    AbsolutelyContinuousOnInterval (e.affineGraph a b) l r :=
  (e.lipschitz_affineGraph a b).lipschitzOnWith.absolutelyContinuousOnInterval

theorem integral_sourceSlope [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ)
    (ha : Function.Injective a) (l r : ℝ) :
    (∫ x in l..r, e.sourceDensity a b a x) = e.affineGraph a b r - e.affineGraph a b l := by
  have heq : (∫ x in l..r, e.sourceDensity a b a x) =
      ∫ x in l..r, deriv (e.affineGraph a b) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_injective_affine (b := b) ha] with x hx _
    exact (e.hasDerivAt_affineGraph a b x hx).deriv.symm
  exact heq.trans (e.absolutelyContinuousOnInterval_affineGraph a b l r).integral_deriv_eq_sub

theorem abs_affineGraph_sub_le_integral_abs_sourceSlope [Fintype ι]
    (e : WallExpr ι) (a b : ι → ℝ) (ha : Function.Injective a) {l r : ℝ} (hlr : l ≤ r) :
    |e.affineGraph a b r - e.affineGraph a b l| ≤
      ∫ x in l..r, e.sourceDensity a b (fun i => |a i|) x := by
  rw [← e.integral_sourceSlope a b ha l r]
  simpa only [sourceDensity] using
    (intervalIntegral.abs_integral_le_integral_abs
      (f := e.sourceDensity a b a) (μ := volume) hlr)

theorem peak_le_integral_abs_sourceSlope [Fintype ι]
    (e : WallExpr ι) (a b : ι → ℝ) (ha : Function.Injective a)
    {l x r : ℝ} (hlx : l ≤ x) (hxr : x ≤ r) :
    2 * e.affineGraph a b x - e.affineGraph a b l - e.affineGraph a b r ≤
      ∫ y in l..r, e.sourceDensity a b (fun i => |a i|) y := by
  have hleft := e.abs_affineGraph_sub_le_integral_abs_sourceSlope a b ha hlx
  have hright := e.abs_affineGraph_sub_le_integral_abs_sourceSlope a b ha hxr
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (e.intervalIntegrable_sourceDensity a b (fun i => |a i|) l x)
    (e.intervalIntegrable_sourceDensity a b (fun i => |a i|) x r)
  linarith [le_abs_self (e.affineGraph a b x - e.affineGraph a b l),
    neg_le_abs (e.affineGraph a b r - e.affineGraph a b x)]

end WallExpr

end AmbidextrousSofa
