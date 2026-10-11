module

public import AmbidextrousSofa.Analysis.ClosedSupportPair
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

/-!
# Closed support derivatives on a proper initial arc

The derivative representative agrees with the actual right tangent
strictly before the final normal and reaches its actual left tangent
at that normal. Thus an atom at the terminal normal remains outside the
closed absolutely continuous arc. Reflection below changes only the
parameter of a function; it does not reflect a maximizing objective.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem absolutelyContinuousOnInterval_comp_const_sub
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b) (c : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => f (c - t)) (c - b) (c - a) := by
  refine absolutelyContinuousOnInterval_of_integral_sub (g := fun t => -deriv f (c - t))
    (hf.intervalIntegrable_deriv.comp_sub_left c).symm.neg fun x hx => ?_
  rw [uIcc_of_le (by linarith)] at hx
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left, sub_sub_cancel,
    (hf.mono (uIcc_subset_uIcc (by rw [uIcc_of_le hab]; constructor <;> linarith [hx.1, hx.2])
      right_mem_uIcc)).integral_deriv_eq_sub]
  ring

theorem ae_hasDerivAt_comp_const_sub
    {f fD : ℝ → ℝ} {a b c : ℝ}
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t) :
    ∀ᵐ t ∂volume.restrict (Ioo (c - b) (c - a)),
      HasDerivAt (fun s => f (c - s)) (-fD (c - t)) t := by
  have hshift := (volume.measurePreserving_sub_left c).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioo).mp hderiv)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with t ht hd
  exact (hd ⟨by linarith [ht.2], by linarith [ht.1]⟩).comp_const_sub c t

theorem IsDownwardCap.closedSupportDerivative_eq_supportTangent_on_arc
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) b ⊆ S) (ht0 : 0 ≤ t) (htb : t < b) :
    closedSupportDerivative U ρ 0 t = supportTangent U t := by
  have := hU.supportTangent_sub_eq_integral_of_density_Ioc hρ hρ0 hρK heq ht0
    fun s hs => hsub ⟨hs.1, hs.2.trans_lt htb⟩
  simp only [closedSupportDerivative, add_zero]
  linarith

/-- The left tangent trace at the final normal is the closed arc's
final derivative. Its atom is not put into the preceding integral. -/
theorem IsDownwardCap.closedSupportDerivative_at_arc_end
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hb : 0 < b) (hsub : Ioo (0 : ℝ) b ⊆ S) :
    closedSupportDerivative U ρ 0 b = MovingSofaOptimality.dot (MovingSofaOptimality.vminus U b) (MovingSofaOptimality.vvec b) := by
  refine tendsto_nhds_unique
    (hU.continuous_closedSupportDerivative hρ hρ0 hρK 0).continuousWithinAt
    (((MovingSofaOptimality.continuous_dot_pair.tendsto _).comp
      ((MovingSofaOptimality.tendsto_vplus_left hU.imported_isConvexBody b).prodMk_nhds
        MovingSofaOptimality.continuous_vvec.continuousWithinAt)).congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT hb] with t ht
  exact (hU.closedSupportDerivative_eq_supportTangent_on_arc hρ hρ0 hρK heq hsub ht.1.le
    ht.2).symm

theorem IsDownwardCap.hasDerivAt_angleSupport_of_open_arc
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) b ⊆ S) (ht : t ∈ Ioo (0 : ℝ) b) :
    HasDerivAt (angleSupport U) (closedSupportDerivative U ρ 0 t) t := by
  rw [hU.closedSupportDerivative_eq_supportTangent_on_arc hρ hρ0 hρK heq hsub ht.1.le ht.2]
  exact hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρK heq (a := t / 2) (b := (t + b) / 2)
    (fun s hs => hsub ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

end AmbidextrousSofa
