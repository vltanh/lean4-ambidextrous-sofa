module

public import AmbidextrousSofa.Analysis.RegularCurvatureDomain
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import AmbidextrousSofa.Analysis.SurfaceAreaFacts

@[expose] public section

/-!
# Support and tangent calculus for the actual curvature density

The support primitive and the support-tangent Stieltjes identity are
objective-independent facts about the actual convex body. Substituting
the proved curvature density turns those identities into ordinary
integral identities, absolute continuity, and the two coupled corner
velocity equations. Every interval used here stays inside the density
domain; its exceptional face atoms are retained outside that domain. The
reflection `t ↦ c - t` keeps absolute continuity and almost-everywhere
derivatives.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- The right tangent coordinate of the actual supporting face. -/
def supportTangent (U : Set Plane) (t : ℝ) : ℝ :=
  MovingSofaOptimality.dot (MovingSofaOptimality.vplus U t) (MovingSofaOptimality.vvec t)

theorem intervalIntegrable_bounded_real_density
    {ρ : ℝ → ℝ} {C : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C) (a b : ℝ) :
    IntervalIntegrable ρ volume a b :=
  (IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hρ.aestronglyMeasurable C
    (.of_forall fun t => (Real.norm_of_nonneg (hρ0 t)).trans_le (hρC t))).intervalIntegrable

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

theorem ae_restrict_Ioo_comp_const_sub {P : ℝ → Prop} {a b c : ℝ}
    (h : ∀ᵐ t ∂volume.restrict (Ioo a b), P t) :
    ∀ᵐ t ∂volume.restrict (Ioo (c - b) (c - a)), P (c - t) := by
  have hshift := (volume.measurePreserving_sub_left c).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioo).mp h)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with t ht hd
  exact hd ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem ae_hasDerivAt_comp_const_sub
    {f fD : ℝ → ℝ} {a b c : ℝ}
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t) :
    ∀ᵐ t ∂volume.restrict (Ioo (c - b) (c - a)),
      HasDerivAt (fun s => f (c - s)) (-fD (c - t)) t :=
  (ae_restrict_Ioo_comp_const_sub hderiv).mono fun t h => h.comp_const_sub c t

theorem IsDownwardCap.angleSupport_shift_sub_eq_integral {U : Set Plane}
    (hU : IsDownwardCap U) (a b d : ℝ) :
    angleSupport U (b + d) - angleSupport U (a + d) =
      ∫ t in a..b, supportTangent U (t + d) := by
  rw [intervalIntegral.integral_comp_add_right]
  exact MovingSofaOptimality.inj_supp_sub_supp hU.imported_isConvexBody _ _

theorem IsDownwardCap.absolutelyContinuousOnInterval_angleSupport_shift
    {U : Set Plane} (hU : IsDownwardCap U) (a b d : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => angleSupport U (t + d)) a b :=
  absolutelyContinuousOnInterval_of_integral_sub
    (MovingSofaOptimality.inj_intervalIntegrable_dvplus hU.imported_isConvexBody d a b)
    fun x _ => hU.angleSupport_shift_sub_eq_integral a x d

theorem IsDownwardCap.absolutelyContinuousOnInterval_angleSupport
    {U : Set Plane} (hU : IsDownwardCap U) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (angleSupport U) a b := by
  simpa only [add_zero] using hU.absolutelyContinuousOnInterval_angleSupport_shift a b 0

theorem IsDownwardCap.intervalIntegrable_shift_density {U : Set Plane}
    (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C : ℝ} (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hρC : ∀ t, ρ t ≤ C) (a b d : ℝ) :
    IntervalIntegrable (fun t => ρ (t + d) - angleSupport U (t + d)) volume a b :=
  (intervalIntegrable_bounded_real_density (hρ.comp (measurable_add_const d))
    (fun _ => hρ0 _) (fun _ => hρC _) a b).sub
    (((continuous_angleSupport hU.isCompact).comp (continuous_add_const d)).intervalIntegrable _ _)

theorem IsDownwardCap.supportTangent_shift_sub_eq_integral_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b d : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Ioc (a + d) (b + d) ⊆ S) :
    supportTangent U (b + d) - supportTangent U (a + d) =
      ∫ t in a..b, ρ (t + d) - angleSupport U (t + d) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  rw [intervalIntegral.integral_comp_add_right (fun t => ρ t - angleSupport U t) d,
    intervalIntegral.integral_sub (intervalIntegrable_bounded_real_density hρ hρ0 hρC _ _)
      ((continuous_angleSupport hU.isCompact).intervalIntegrable _ _),
    intervalIntegral.integral_of_le (by linarith),
    ← measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub]
  exact dot_vplus_vvec_sub hU.imported_isConvexBody (by linarith)

theorem IsDownwardCap.absolutelyContinuousOnInterval_supportTangent_shift_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b d : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc (a + d) (b + d) ⊆ S) :
    AbsolutelyContinuousOnInterval (fun t => supportTangent U (t + d)) a b := by
  refine absolutelyContinuousOnInterval_of_integral_sub
    (hU.intervalIntegrable_shift_density hρ hρ0 hρC a b d) fun x hx => ?_
  rw [uIcc_of_le hab] at hx
  exact hU.supportTangent_shift_sub_eq_integral_of_density hρ hρ0 hρC heq hx.1
    fun s hs => hsub ⟨hs.1.le, by linarith [hs.2, hx.2]⟩

theorem IsDownwardCap.absolutelyContinuousOnInterval_supportTangent_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc a b ⊆ S) :
    AbsolutelyContinuousOnInterval (supportTangent U) a b := by
  simpa only [add_zero] using
    hU.absolutelyContinuousOnInterval_supportTangent_shift_of_density hρ hρ0 hρC heq hab
      (d := 0) (by simpa only [add_zero] using hsub)

theorem IsDownwardCap.hasDerivAt_angleSupport_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Icc a b ⊆ S) (hx : x ∈ Ioo a b) :
    HasDerivAt (angleSupport U) (supportTangent U x) x := by
  have hab : a ≤ b := (hx.1.trans hx.2).le
  have hcx := (hU.absolutelyContinuousOnInterval_supportTangent_of_density hρ hρ0 hρC heq hab
    hsub).continuousOn.continuousAt (by rw [uIcc_of_le hab]; exact Icc_mem_nhds hx.1 hx.2)
  have hi := MovingSofaOptimality.inj_intervalIntegrable_dvplus hU.imported_isConvexBody 0 a x
  simp only [add_zero] at hi
  refine ((intervalIntegral.integral_hasDerivAt_right hi
    hU.measurable_supportTangent.aestronglyMeasurable.stronglyMeasurableAtFilter hcx).const_add
      (angleSupport U a)).congr_of_eventuallyEq (.of_forall fun t => ?_)
  have := MovingSofaOptimality.inj_supp_sub_supp hU.imported_isConvexBody a t
  simp only [angleSupport_eq_imported_supp] at *
  linarith

theorem IsDownwardCap.ae_hasDerivAt_supportTangent_shift_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b d : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc (a + d) (b + d) ⊆ S) :
    ∀ᵐ x ∂volume.restrict (Ioo a b),
      HasDerivAt (fun t => supportTangent U (t + d))
        (ρ (x + d) - angleSupport U (x + d)) x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae
    (hU.intervalIntegrable_shift_density hρ hρ0 hρC a b d).ae_hasDerivAt_integral]
    with x hx hdx
  refine ((hdx (by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self hx) a left_mem_uIcc).const_add
    (supportTangent U (a + d))).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
  have := hU.supportTangent_shift_sub_eq_integral_of_density hρ hρ0 hρC heq ht.1.le
    fun s hs => hsub ⟨hs.1.le, by linarith [hs.2, ht.2]⟩
  linarith

theorem IsDownwardCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hbase : Icc a b ⊆ S)
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    AbsolutelyContinuousOnInterval (firstCornerVelocity U) a b ∧
      AbsolutelyContinuousOnInterval (secondCornerVelocity U) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact ⟨((hU.absolutelyContinuousOnInterval_angleSupport a b).add
      (hU.absolutelyContinuousOnInterval_supportTangent_shift_of_density hρ hρ0 hρC heq hab
        hshift)).sub hc,
    ((hU.absolutelyContinuousOnInterval_angleSupport_shift a b (Real.pi / 2)).sub
      (hU.absolutelyContinuousOnInterval_supportTangent_of_density hρ hρ0 hρC heq hab
        hbase)).sub hc⟩

/-- The actual two corner velocities satisfy the coupled support equations
almost everywhere, with the same actual curvature density. -/
theorem IsDownwardCap.ae_hasDerivAt_cornerVelocities_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hbase : Icc a b ⊆ S)
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    ∀ᵐ x ∂volume.restrict (Ioo a b),
      HasDerivAt (firstCornerVelocity U)
        (ρ (x + Real.pi / 2) - secondCornerVelocity U x - 1) x ∧
      HasDerivAt (secondCornerVelocity U)
        (firstCornerVelocity U x + 1 - ρ x) x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.ae_hasDerivAt_supportTangent_shift_of_density hρ hρ0 hρC heq hab (d := 0)
      (by simpa only [add_zero] using hbase),
    hU.ae_hasDerivAt_supportTangent_shift_of_density hρ hρ0 hρC heq hab hshift]
    with x hx hdt hdts
  simp only [add_zero] at hdt
  have hds := hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hbase hx
  have hdss := (hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hshift
    ⟨by linarith [hx.1], by linarith [hx.2]⟩).comp_add_const x (Real.pi / 2)
  refine ⟨((hds.add hdts).sub_const 1).congr_deriv ?_,
    ((hdss.sub hdt).sub_const 1).congr_deriv ?_⟩ <;>
  · simp only [firstCornerVelocity, secondCornerVelocity, supportTangent,
      angleSupport_eq_imported_supp]
    ring

end AmbidextrousSofa
