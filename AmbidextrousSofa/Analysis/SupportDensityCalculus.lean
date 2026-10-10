import AmbidextrousSofa.Analysis.RegularCurvatureDomain
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Support and tangent calculus for the actual curvature density

The support primitive and the support-tangent Stieltjes identity are
objective-independent facts about the actual convex body. Substituting
the proved curvature density turns those identities into ordinary
integral identities, absolute continuity, and the two coupled corner
velocity equations. Every interval used here stays inside the density
domain; its exceptional face atoms are retained outside that domain.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The right tangent coordinate of the actual supporting face. -/
def supportTangent (U : Set Plane) (t : ℝ) : ℝ :=
  Imported.dot (Imported.vplus U t) (Imported.vvec t)

theorem intervalIntegrable_bounded_real_density
    {ρ : ℝ → ℝ} {C : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C) (a b : ℝ) :
    IntervalIntegrable ρ volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hρ.aestronglyMeasurable C
  exact Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact hρC t)

/-- An exact integral representation supplies absolute continuity. -/
theorem absolutelyContinuousOnInterval_of_integral_sub
    {f g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (heq : ∀ x ∈ uIcc a b, f x - f a = ∫ t in a..x, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hi := hg.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : a ∈ uIcc a b)
  apply (hc.add hi).congr
  intro x hx
  change f a + (∫ t in a..x, g t) = f x
  linarith [heq x hx]

theorem IsDownwardCap.intervalIntegrable_supportTangent {U : Set Plane}
    (hU : IsDownwardCap U) (a b : ℝ) :
    IntervalIntegrable (supportTangent U) volume a b := by
  simpa only [supportTangent, add_zero] using
    Imported.inj_intervalIntegrable_dvplus hU.imported_isConvexBody 0 a b

theorem IsDownwardCap.angleSupport_sub_eq_integral {U : Set Plane}
    (hU : IsDownwardCap U) (a b : ℝ) :
    angleSupport U b - angleSupport U a = ∫ t in a..b, supportTangent U t :=
  Imported.inj_supp_sub_supp hU.imported_isConvexBody a b

theorem IsDownwardCap.angleSupport_shift_sub_eq_integral {U : Set Plane}
    (hU : IsDownwardCap U) (a b d : ℝ) :
    angleSupport U (b + d) - angleSupport U (a + d) =
      ∫ t in a..b, supportTangent U (t + d) := by
  rw [intervalIntegral.integral_comp_add_right]
  exact hU.angleSupport_sub_eq_integral _ _

theorem IsDownwardCap.absolutelyContinuousOnInterval_angleSupport_shift
    {U : Set Plane} (hU : IsDownwardCap U) (a b d : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => angleSupport U (t + d)) a b := by
  apply absolutelyContinuousOnInterval_of_integral_sub
    (Imported.inj_intervalIntegrable_dvplus hU.imported_isConvexBody d a b)
  intro x _
  exact hU.angleSupport_shift_sub_eq_integral a x d

theorem IsDownwardCap.absolutelyContinuousOnInterval_angleSupport
    {U : Set Plane} (hU : IsDownwardCap U) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (angleSupport U) a b := by
  simpa only [add_zero] using hU.absolutelyContinuousOnInterval_angleSupport_shift a b 0

theorem IsDownwardCap.supportTangent_sub_eq_integral_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc a b ⊆ S) :
    supportTangent U b - supportTangent U a =
      ∫ t in a..b, ρ t - angleSupport U t := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [sub_self, intervalIntegral.integral_same]
  · have hmass : (Imported.sigma U (Ioc a b)).toReal = ∫ t in a..b, ρ t := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc
        (Ioc_subset_Icc_self.trans hsub)
    change Imported.dot (Imported.vplus U b) (Imported.vvec b) -
      Imported.dot (Imported.vplus U a) (Imported.vvec a) = _
    rw [Imported.inj_dot_vplus_vvec_sub hU.imported_isConvexBody hab, hmass,
      intervalIntegral.integral_sub
        (intervalIntegrable_bounded_real_density hρ hρ0 hρC a b)
        (hU.imported_isConvexBody.continuous_supp.intervalIntegrable a b)]

theorem IsDownwardCap.supportTangent_shift_sub_eq_integral_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b d : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc (a + d) (b + d) ⊆ S) :
    supportTangent U (b + d) - supportTangent U (a + d) =
      ∫ t in a..b, ρ (t + d) - angleSupport U (t + d) := by
  rw [intervalIntegral.integral_comp_add_right
    (fun t => ρ t - angleSupport U t) d]
  exact hU.supportTangent_sub_eq_integral_of_density hρ hρ0 hρC heq
    (add_le_add_right hab d) hsub

theorem IsDownwardCap.absolutelyContinuousOnInterval_supportTangent_shift_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b d : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc (a + d) (b + d) ⊆ S) :
    AbsolutelyContinuousOnInterval (fun t => supportTangent U (t + d)) a b := by
  have hρi : IntervalIntegrable (fun t => ρ (t + d)) volume a b :=
    intervalIntegrable_bounded_real_density
      (hρ.comp (measurable_id.add_const d)) (fun t => hρ0 (t + d))
      (fun t => hρC (t + d)) a b
  have hhi : IntervalIntegrable (fun t => angleSupport U (t + d)) volume a b :=
    (hU.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const d)).intervalIntegrable a b
  apply absolutelyContinuousOnInterval_of_integral_sub (hρi.sub hhi)
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact hU.supportTangent_shift_sub_eq_integral_of_density hρ hρ0 hρC heq hx.1
    ((Icc_subset_Icc le_rfl (add_le_add_right hx.2 d)).trans hsub)

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
  have hac := hU.absolutelyContinuousOnInterval_supportTangent_of_density
    hρ hρ0 hρC heq hab hsub
  have hcont : ContinuousOn (supportTangent U) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hac.continuousOn
  have hcx : ContinuousAt (supportTangent U) x :=
    (hcont x ⟨hx.1.le, hx.2.le⟩).continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hU.intervalIntegrable_supportTangent a x)
    hU.measurable_supportTangent.aestronglyMeasurable.stronglyMeasurableAtFilter hcx).const_add
      (angleSupport U a)
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => by
    change angleSupport U t = angleSupport U a + (∫ s in a..t, supportTangent U s)
    linarith [hU.angleSupport_sub_eq_integral a t])

theorem IsDownwardCap.ae_hasDerivAt_supportTangent_shift_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b d : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc (a + d) (b + d) ⊆ S) :
    ∀ᵐ x ∂volume.restrict (Ioo a b),
      HasDerivAt (fun t => supportTangent U (t + d))
        (ρ (x + d) - angleSupport U (x + d)) x := by
  have hρi : IntervalIntegrable (fun t => ρ (t + d)) volume a b :=
    intervalIntegrable_bounded_real_density
      (hρ.comp (measurable_id.add_const d)) (fun t => hρ0 (t + d))
      (fun t => hρC (t + d)) a b
  have hhi : IntervalIntegrable (fun t => angleSupport U (t + d)) volume a b :=
    (hU.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const d)).intervalIntegrable a b
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (hρi.sub hhi).ae_hasDerivAt_integral] with x hx hdx
  have hxmem : x ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨hx.1.le, hx.2.le⟩
  have hd := (hdx hxmem a left_mem_uIcc).const_add (supportTangent U (a + d))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
  change supportTangent U (t + d) = supportTangent U (a + d) +
    (∫ s in a..t, ρ (s + d) - angleSupport U (s + d))
  have hid := hU.supportTangent_shift_sub_eq_integral_of_density hρ hρ0 hρC heq ht.1.le
    ((Icc_subset_Icc le_rfl (add_le_add_right ht.2.le d)).trans hsub)
  linarith

theorem IsDownwardCap.ae_hasDerivAt_supportTangent_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc a b ⊆ S) :
    ∀ᵐ x ∂volume.restrict (Ioo a b),
      HasDerivAt (supportTangent U) (ρ x - angleSupport U x) x := by
  simpa only [add_zero] using hU.ae_hasDerivAt_supportTangent_shift_of_density
    hρ hρ0 hρC heq hab (d := 0) (by simpa only [add_zero] using hsub)

theorem IsDownwardCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hbase : Icc a b ⊆ S)
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    AbsolutelyContinuousOnInterval (firstCornerVelocity U) a b ∧
      AbsolutelyContinuousOnInterval (secondCornerVelocity U) a b := by
  have hs := hU.absolutelyContinuousOnInterval_angleSupport a b
  have hss := hU.absolutelyContinuousOnInterval_angleSupport_shift a b (Real.pi / 2)
  have ht := hU.absolutelyContinuousOnInterval_supportTangent_of_density
    hρ hρ0 hρC heq hab hbase
  have hts := hU.absolutelyContinuousOnInterval_supportTangent_shift_of_density
    hρ hρ0 hρC heq hab hshift
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact ⟨(hs.add hts).sub hc, (hss.sub ht).sub hc⟩

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
    hU.ae_hasDerivAt_supportTangent_of_density hρ hρ0 hρC heq hab hbase,
    hU.ae_hasDerivAt_supportTangent_shift_of_density hρ hρ0 hρC heq hab hshift]
    with x hx hdt hdts
  have hds := hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hbase hx
  have hdx := hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hshift
    (show x + Real.pi / 2 ∈ Ioo (a + Real.pi / 2) (b + Real.pi / 2) from
      ⟨add_lt_add_right hx.1 _, add_lt_add_right hx.2 _⟩)
  have hdss : HasDerivAt (fun t => angleSupport U (t + Real.pi / 2))
      (supportTangent U (x + Real.pi / 2)) x := by
    simpa only [Function.comp_def, mul_one] using
      hdx.comp x ((hasDerivAt_id x).add_const (Real.pi / 2))
  have hd1 : HasDerivAt (firstCornerVelocity U)
      (supportTangent U x + (ρ (x + Real.pi / 2) - angleSupport U (x + Real.pi / 2))) x :=
    (hds.add hdts).sub_const 1
  have hd2 : HasDerivAt (secondCornerVelocity U)
      (supportTangent U (x + Real.pi / 2) - (ρ x - angleSupport U x)) x :=
    (hdss.sub hdt).sub_const 1
  constructor
  · apply hd1.congr_deriv
    change supportTangent U x + (ρ (x + Real.pi / 2) - angleSupport U (x + Real.pi / 2)) =
      ρ (x + Real.pi / 2) -
        (angleSupport U (x + Real.pi / 2) - supportTangent U x - 1) - 1
    ring
  · apply hd2.congr_deriv
    change supportTangent U (x + Real.pi / 2) - (ρ x - angleSupport U x) =
      (angleSupport U x + supportTangent U (x + Real.pi / 2) - 1) + 1 - ρ x
    ring

/-- The first actual velocity equation in integrated form. -/
theorem IsDownwardCap.firstCornerVelocity_sub_eq_integral_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    firstCornerVelocity U b - firstCornerVelocity U a =
      ∫ t in a..b, ρ (t + Real.pi / 2) - secondCornerVelocity U t - 1 := by
  have hρi : IntervalIntegrable (fun t => ρ (t + Real.pi / 2)) volume a b :=
    intervalIntegrable_bounded_real_density
      (hρ.comp (measurable_id.add_const (Real.pi / 2)))
      (fun t => hρ0 _) (fun t => hρC _) a b
  have hhi : IntervalIntegrable (fun t => angleSupport U (t + Real.pi / 2)) volume a b :=
    (hU.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const (Real.pi / 2))).intervalIntegrable a b
  have hτ := hU.supportTangent_shift_sub_eq_integral_of_density hρ hρ0 hρC heq hab hshift
  calc
    firstCornerVelocity U b - firstCornerVelocity U a =
        (angleSupport U b - angleSupport U a) +
          (supportTangent U (b + Real.pi / 2) - supportTangent U (a + Real.pi / 2)) := by
      change (_ + _ - 1) - (_ + _ - 1) = _
      ring
    _ = (∫ t in a..b, supportTangent U t) +
        (∫ t in a..b, ρ (t + Real.pi / 2) - angleSupport U (t + Real.pi / 2)) := by
      rw [hU.angleSupport_sub_eq_integral, hτ]
    _ = ∫ t in a..b, supportTangent U t +
        (ρ (t + Real.pi / 2) - angleSupport U (t + Real.pi / 2)) :=
      (intervalIntegral.integral_add (hU.intervalIntegrable_supportTangent a b)
        (hρi.sub hhi)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change supportTangent U t + (ρ (t + Real.pi / 2) - angleSupport U (t + Real.pi / 2)) =
        ρ (t + Real.pi / 2) -
          (angleSupport U (t + Real.pi / 2) - supportTangent U t - 1) - 1
      ring

/-- The second actual velocity equation in integrated form. -/
theorem IsDownwardCap.secondCornerVelocity_sub_eq_integral_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hbase : Icc a b ⊆ S) :
    secondCornerVelocity U b - secondCornerVelocity U a =
      ∫ t in a..b, firstCornerVelocity U t + 1 - ρ t := by
  have hτi : IntervalIntegrable (fun t => supportTangent U (t + Real.pi / 2)) volume a b :=
    Imported.inj_intervalIntegrable_dvplus hU.imported_isConvexBody (Real.pi / 2) a b
  have hρi := intervalIntegrable_bounded_real_density hρ hρ0 hρC a b
  have hhi := hU.imported_isConvexBody.continuous_supp.intervalIntegrable a b
  have hτ := hU.supportTangent_sub_eq_integral_of_density hρ hρ0 hρC heq hab hbase
  calc
    secondCornerVelocity U b - secondCornerVelocity U a =
        (angleSupport U (b + Real.pi / 2) - angleSupport U (a + Real.pi / 2)) -
          (supportTangent U b - supportTangent U a) := by
      change (_ - _ - 1) - (_ - _ - 1) = _
      ring
    _ = (∫ t in a..b, supportTangent U (t + Real.pi / 2)) -
        (∫ t in a..b, ρ t - angleSupport U t) := by
      rw [hU.angleSupport_shift_sub_eq_integral, hτ]
    _ = ∫ t in a..b, supportTangent U (t + Real.pi / 2) - (ρ t - angleSupport U t) :=
      (intervalIntegral.integral_sub hτi (hρi.sub hhi)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change supportTangent U (t + Real.pi / 2) - (ρ t - angleSupport U t) =
        (angleSupport U t + supportTangent U (t + Real.pi / 2) - 1) + 1 - ρ t
      ring

end AmbidextrousSofa
