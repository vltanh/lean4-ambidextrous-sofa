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
open scoped Topology

namespace AmbidextrousSofa

theorem absolutelyContinuousOnInterval_comp_const_sub
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b) (c : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => f (c - t)) (c - b) (c - a) := by
  have hi : IntervalIntegrable (fun t => -deriv f (c - t)) volume (c - b) (c - a) :=
    (hf.intervalIntegrable_deriv.comp_sub_left c).symm.neg
  apply absolutelyContinuousOnInterval_of_integral_sub hi
  intro x hx
  rw [uIcc_of_le (sub_le_sub_left hab c)] at hx
  have hleft : a ≤ c - x := by linarith only [hx.2]
  have hright : c - x ≤ b := by linarith only [hx.1]
  have hxb : AbsolutelyContinuousOnInterval f (c - x) b := hf.mono (by
    rw [uIcc_of_le hab, uIcc_of_le hright]
    exact Icc_subset_Icc hleft le_rfl)
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left,
    sub_sub_cancel, hxb.integral_deriv_eq_sub]
  ring

theorem ae_hasDerivAt_comp_const_sub
    {f fD : ℝ → ℝ} {a b c : ℝ}
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t) :
    ∀ᵐ t ∂volume.restrict (Ioo (c - b) (c - a)),
      HasDerivAt (fun s => f (c - s)) (-fD (c - t)) t := by
  have hglobal := (ae_restrict_iff' measurableSet_Ioo).mp hderiv
  have hshift := (volume.measurePreserving_sub_left c).quasiMeasurePreserving.ae hglobal
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift]
    with t ht hd
  have hmem : c - t ∈ Ioo a b := by
    constructor <;> linarith only [ht.1, ht.2]
  simpa only [Function.comp_def, sub_self, zero_sub, mul_neg_one] using
    (hd hmem).comp t ((hasDerivAt_const t c).sub (hasDerivAt_id t))

theorem IsDownwardCap.closedSupportDerivative_eq_supportTangent_on_arc
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) b ⊆ S) (ht0 : 0 ≤ t) (htb : t < b) :
    closedSupportDerivative U ρ 0 t = supportTangent U t := by
  have hid := hU.supportTangent_sub_eq_integral_of_density_Ioc hρ hρ0 hρK heq
    ht0 (by
      intro s hs
      exact hsub ⟨hs.1, hs.2.trans_lt htb⟩)
  dsimp only [closedSupportDerivative]
  simp only [add_zero]
  linarith only [hid]

/-- The left tangent trace at the final normal is the closed arc's
final derivative. Its atom is not put into the preceding integral. -/
theorem IsDownwardCap.closedSupportDerivative_at_arc_end
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hb : 0 < b) (hsub : Ioo (0 : ℝ) b ⊆ S) :
    closedSupportDerivative U ρ 0 b = MovingSofaOptimality.dot (MovingSofaOptimality.vminus U b) (MovingSofaOptimality.vvec b) := by
  have hp := MovingSofaOptimality.tendsto_vplus_left hU.imported_isConvexBody b
  have hv := (MovingSofaOptimality.continuous_vvec.tendsto b).mono_left
    (nhdsWithin_le_nhds : 𝓝[<] b ≤ 𝓝 b)
  have htangent := (MovingSofaOptimality.continuous_dot_pair.tendsto
    (MovingSofaOptimality.vminus U b, MovingSofaOptimality.vvec b)).comp (hp.prodMk_nhds hv)
  have hclosed : Tendsto (closedSupportDerivative U ρ 0) (𝓝[<] b)
      (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vminus U b) (MovingSofaOptimality.vvec b))) := by
    apply htangent.congr'
    filter_upwards [Ioo_mem_nhdsLT hb] with t ht
    exact (hU.closedSupportDerivative_eq_supportTangent_on_arc
      hρ hρ0 hρK heq hsub ht.1.le ht.2).symm
  exact tendsto_nhds_unique
    ((hU.continuous_closedSupportDerivative hρ hρ0 hρK 0).tendsto b |>.mono_left nhdsWithin_le_nhds)
    hclosed

theorem IsDownwardCap.hasDerivAt_angleSupport_of_open_arc
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) b ⊆ S) (ht : t ∈ Ioo (0 : ℝ) b) :
    HasDerivAt (angleSupport U) (closedSupportDerivative U ρ 0 t) t := by
  rw [hU.closedSupportDerivative_eq_supportTangent_on_arc hρ hρ0 hρK heq hsub ht.1.le ht.2]
  apply hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρK heq
    (a := t / 2) (b := (t + b) / 2)
  · intro s hs
    apply hsub
    constructor <;> linarith only [ht.1, ht.2, hs.1, hs.2]
  · constructor <;> linarith only [ht.1, ht.2]

theorem IsDownwardCap.angleSupport_eq_closed_primitive_on_arc
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) b ⊆ S) (ht : t ∈ Icc (0 : ℝ) b) :
    angleSupport U t = angleSupport U 0 + ∫ s in (0 : ℝ)..t, closedSupportDerivative U ρ 0 s := by
  have hid := hU.angleSupport_sub_eq_integral 0 t
  have hi : (∫ s in (0 : ℝ)..t, supportTangent U s) =
      ∫ s in (0 : ℝ)..t, closedSupportDerivative U ρ 0 s := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    exact (hU.closedSupportDerivative_eq_supportTangent_on_arc hρ hρ0 hρK heq hsub
      hs.1.le (hs.2.trans_le ht.2)).symm
  rw [hi] at hid
  linarith only [hid]

theorem IsDownwardCap.hasDerivWithinAt_angleSupport_closed_arc
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) b ⊆ S) (ht : t ∈ Icc (0 : ℝ) b) :
    HasDerivWithinAt (angleSupport U) (closedSupportDerivative U ρ 0 t) (Icc 0 b) t := by
  have hd := ((hU.continuous_closedSupportDerivative hρ hρ0 hρK 0).integral_hasStrictDerivAt
    0 t).hasDerivAt.const_add (angleSupport U 0)
  exact hd.hasDerivWithinAt.congr_of_mem
    (fun s hs => hU.angleSupport_eq_closed_primitive_on_arc hρ hρ0 hρK heq hsub hs) ht

end AmbidextrousSofa
