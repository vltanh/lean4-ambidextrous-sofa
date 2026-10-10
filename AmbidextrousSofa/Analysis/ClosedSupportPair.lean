module

public import AmbidextrousSofa.Analysis.SupportDensityCalculus
public import AmbidextrousSofa.Analysis.TangencyEndpoints
public import AmbidextrousSofa.Analysis.QuarterFunctions
public import AmbidextrousSofa.Measure.SupportArea
public import AmbidextrousSofa.Analysis.SurfaceAreaFacts

@[expose] public section

/-!
# Closed support quarters from actual open curvature densities

The derivative representative starts at the right endpoint of the initial
supporting face and is continued by its actual curvature integral. At the
terminal normal it reaches the left endpoint of that face. Thus neither the
top atom nor the axis faces are absorbed into a Lebesgue density.

The two quarters may belong to different actual caps. This includes both a
horizontal cap and the low companion wing of a tilted cap.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def closedSupportDerivative (U : Set Plane) (ρ : ℝ → ℝ) (d t : ℝ) : ℝ :=
  supportTangent U d + ∫ s in (0 : ℝ)..t, ρ (s + d) - angleSupport U (s + d)

theorem IsDownwardCap.intervalIntegrable_shifted_density_sub_support
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (a b d : ℝ) :
    IntervalIntegrable (fun t => ρ (t + d) - angleSupport U (t + d)) volume a b :=
  (intervalIntegrable_bounded_real_density
    (hρ.comp (measurable_id.add_const d)) (fun t => hρ0 (t + d))
    (fun t => hρK (t + d)) a b).sub
    ((hU.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const d)).intervalIntegrable a b)

theorem IsDownwardCap.continuous_closedSupportDerivative
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) (d : ℝ) :
    Continuous (closedSupportDerivative U ρ d) :=
  continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => hU.intervalIntegrable_shifted_density_sub_support hρ hρ0 hρK a b d) 0)

theorem IsDownwardCap.absolutelyContinuousOnInterval_closedSupportDerivative
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (a b d : ℝ) :
    AbsolutelyContinuousOnInterval (closedSupportDerivative U ρ d) a b := by
  apply absolutelyContinuousOnInterval_of_integral_sub
    (hU.intervalIntegrable_shifted_density_sub_support hρ hρ0 hρK a b d)
  intro x _
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_shifted_density_sub_support hρ hρ0 hρK 0 a d)
    (hU.intervalIntegrable_shifted_density_sub_support hρ hρ0 hρK a x d)
  dsimp only [closedSupportDerivative]
  linarith

theorem IsDownwardCap.ae_hasDerivAt_closedSupportDerivative
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hab : a ≤ b) (d : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (closedSupportDerivative U ρ d)
        (ρ (t + d) - angleSupport U (t + d)) t := by
  have hi := hU.intervalIntegrable_shifted_density_sub_support hρ hρ0 hρK
    (min 0 a) (max 0 b) d
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae hi.ae_hasDerivAt_integral] with t ht hdt
  have hbig : min 0 a ≤ max 0 b := (min_le_left _ _).trans (le_max_left _ _)
  have htbig : t ∈ uIcc (min 0 a) (max 0 b) := by
    rw [uIcc_of_le hbig]
    exact ⟨(min_le_right _ _).trans ht.1.le, ht.2.le.trans (le_max_right _ _)⟩
  have hzero : (0 : ℝ) ∈ uIcc (min 0 a) (max 0 b) := by
    rw [uIcc_of_le hbig]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  exact (hdt htbig 0 hzero).const_add (supportTangent U d)

/-- Only the half-open Stieltjes interval must lie in the density domain.
The initial face atom is deliberately excluded. -/
theorem IsDownwardCap.supportTangent_sub_eq_integral_of_density_Ioc
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Ioc a b ⊆ S) :
    supportTangent U b - supportTangent U a =
      ∫ t in a..b, ρ t - angleSupport U t := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [sub_self, intervalIntegral.integral_same]
  · have hmass : (MovingSofaOptimality.sigma U (Ioc a b)).toReal = ∫ t in a..b, ρ t := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq
        measurableSet_Ioc hsub
    change MovingSofaOptimality.dot (MovingSofaOptimality.vplus U b) (MovingSofaOptimality.vvec b) -
      MovingSofaOptimality.dot (MovingSofaOptimality.vplus U a) (MovingSofaOptimality.vvec a) = _
    rw [AmbidextrousSofa.dot_vplus_vvec_sub hU.imported_isConvexBody hab, hmass,
      intervalIntegral.integral_sub
        (intervalIntegrable_bounded_real_density hρ hρ0 hρK a b)
        (hU.imported_isConvexBody.continuous_supp.intervalIntegrable a b)]

theorem IsDownwardCap.closedSupportDerivative_eq_supportTangent
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K d t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo d (d + Real.pi / 2) ⊆ S)
    (ht0 : 0 ≤ t) (htL : t < Real.pi / 2) :
    closedSupportDerivative U ρ d t = supportTangent U (t + d) := by
  have hid := hU.supportTangent_sub_eq_integral_of_density_Ioc hρ hρ0 hρK heq
    (a := d) (b := t + d) (by linarith) (by
      intro s hs
      apply hsub
      exact ⟨hs.1, by linarith [hs.2]⟩)
  have hshift : (∫ s in (0 : ℝ)..t, ρ (s + d) - angleSupport U (s + d)) =
      ∫ s in d..t + d, ρ s - angleSupport U s := by
    simpa only [zero_add] using intervalIntegral.integral_comp_add_right
      (fun s => ρ s - angleSupport U s) d (a := 0) (b := t)
  rw [← hshift] at hid
  dsimp only [closedSupportDerivative]
  linarith

theorem IsDownwardCap.closedSupportDerivative_at_end
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K d : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Ioo d (d + Real.pi / 2) ⊆ S) :
    closedSupportDerivative U ρ d (Real.pi / 2) =
      MovingSofaOptimality.dot (MovingSofaOptimality.vminus U (Real.pi / 2 + d))
        (MovingSofaOptimality.vvec (Real.pi / 2 + d)) := by
  have hp := (MovingSofaOptimality.tendsto_vplus_left hU.imported_isConvexBody
    (Real.pi / 2 + d)).comp (tendsto_add_const_nhdsLT (Real.pi / 2) d)
  have hv := ((MovingSofaOptimality.continuous_vvec.comp (continuous_id.add_const d)).tendsto
    (Real.pi / 2)).mono_left (nhdsWithin_le_nhds :
      𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
  have htangent := (MovingSofaOptimality.continuous_dot_pair.tendsto
    (MovingSofaOptimality.vminus U (Real.pi / 2 + d), MovingSofaOptimality.vvec (Real.pi / 2 + d))).comp
      (hp.prodMk_nhds hv)
  have hclosed : Tendsto (closedSupportDerivative U ρ d) (𝓝[<] (Real.pi / 2))
      (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vminus U (Real.pi / 2 + d))
        (MovingSofaOptimality.vvec (Real.pi / 2 + d)))) := by
    apply htangent.congr'
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
      with t ht
    exact (hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq hsub ht.1.le ht.2).symm
  exact tendsto_nhds_unique
    ((hU.continuous_closedSupportDerivative hρ hρ0 hρK d).tendsto
      (Real.pi / 2) |>.mono_left nhdsWithin_le_nhds) hclosed

@[simp] theorem closedSupportDerivative_zero (U : Set Plane) (ρ : ℝ → ℝ) (d : ℝ) :
    closedSupportDerivative U ρ d 0 = supportTangent U d := by
  simp only [closedSupportDerivative, intervalIntegral.integral_same, add_zero]

theorem IsDownwardCap.hasDerivAt_shiftedSupport_of_open_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K d t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo d (d + Real.pi / 2) ⊆ S) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun s => angleSupport U (s + d)) (closedSupportDerivative U ρ d t) t := by
  rw [hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq hsub ht.1.le ht.2]
  have hI : Icc (d + t / 2) (d + (t + Real.pi / 2) / 2) ⊆ S := by
    intro s hs
    apply hsub
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  have hx : t + d ∈ Ioo (d + t / 2) (d + (t + Real.pi / 2) / 2) := by
    constructor <;> linarith [ht.1, ht.2]
  have hd := hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρK heq hI hx
  simpa only [Function.comp_def, mul_one] using
    hd.comp t ((hasDerivAt_id t).add_const d)

theorem IsDownwardCap.shiftedSupport_eq_closed_primitive
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K d t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo d (d + Real.pi / 2) ⊆ S) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    angleSupport U (t + d) = angleSupport U d +
      ∫ s in (0 : ℝ)..t, closedSupportDerivative U ρ d s := by
  have hprimitive := hU.angleSupport_shift_sub_eq_integral 0 t d
  simp only [zero_add] at hprimitive
  have hi : (∫ s in (0 : ℝ)..t, supportTangent U (s + d)) =
      ∫ s in (0 : ℝ)..t, closedSupportDerivative U ρ d s := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    exact (hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq hsub hs.1.le
      (hs.2.trans_le ht.2)).symm
  rw [hi] at hprimitive
  linarith

/-- Differentiation within the closed quarter includes the true initial
right derivative and terminal left derivative. -/
theorem IsDownwardCap.hasDerivWithinAt_shiftedSupport_closed
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K d t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo d (d + Real.pi / 2) ⊆ S) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    HasDerivWithinAt (fun s => angleSupport U (s + d))
      (closedSupportDerivative U ρ d t) (Icc 0 (Real.pi / 2)) t := by
  have hd := ((hU.continuous_closedSupportDerivative hρ hρ0 hρK d).integral_hasStrictDerivAt
    0 t).hasDerivAt.const_add (angleSupport U d)
  exact hd.hasDerivWithinAt.congr_of_mem
    (fun s hs => hU.shiftedSupport_eq_closed_primitive hρ hρ0 hρK heq hsub hs) ht

/-- The actual support in each of two quarters, with closed continuous
derivative representatives. The second cap may be a companion cut. -/
def supportQuarterPair {U V : Set Plane} (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    {ρ σ : ℝ → ℝ} {K J : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hσ : Measurable σ) (hσ0 : ∀ t, 0 ≤ σ t) (hσJ : ∀ t, σ t ≤ J)
    (hfirst : (upperCurvature U).restrict (Ioo 0 (Real.pi / 2)) =
      (volume.restrict (Ioo 0 (Real.pi / 2))).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsecond : (upperCurvature V).restrict (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (σ t))) : Analysis.QuarterPair where
  f := angleSupport U
  g := fun t => angleSupport V (t + Real.pi / 2)
  fD := closedSupportDerivative U ρ 0
  gD := closedSupportDerivative V σ (Real.pi / 2)
  continuous_f := hU.imported_isConvexBody.continuous_supp.continuousOn
  continuous_g := (hV.imported_isConvexBody.continuous_supp.comp
    (continuous_id.add_const (Real.pi / 2))).continuousOn
  continuous_fD := (hU.continuous_closedSupportDerivative hρ hρ0 hρK 0).continuousOn
  continuous_gD := (hV.continuous_closedSupportDerivative hσ hσ0 hσJ (Real.pi / 2)).continuousOn
  hasDeriv_f := by
    intro t ht
    have hd := hU.hasDerivAt_shiftedSupport_of_open_density hρ hρ0 hρK hfirst
      (d := 0) (by simpa only [zero_add] using (Subset.rfl :
        Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2))) ht
    simpa only [add_zero] using hd.hasDerivWithinAt (s := Ioi t)
  hasDeriv_g := by
    intro t ht
    exact (hV.hasDerivAt_shiftedSupport_of_open_density hσ hσ0 hσJ hsecond
      (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩) ht).hasDerivWithinAt

/-- Absolute continuity and the coupled equations hold on the whole closed
quarter, including its genuine one-sided endpoint traces. -/
theorem supportQuarterPair_corner_calculus
    {U V : Set Plane} (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    {ρ σ : ℝ → ℝ} {K J : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hσ : Measurable σ) (hσ0 : ∀ t, 0 ≤ σ t) (hσJ : ∀ t, σ t ≤ J)
    (hfirst : (upperCurvature U).restrict (Ioo 0 (Real.pi / 2)) =
      (volume.restrict (Ioo 0 (Real.pi / 2))).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsecond : (upperCurvature V).restrict (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (σ t))) :
    let F := supportQuarterPair hU hV hρ hρ0 hρK hσ hσ0 hσJ hfirst hsecond
    AbsolutelyContinuousOnInterval (supportP F.fD F.g) 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (supportQ F.gD F.f) 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        HasDerivAt (supportP F.fD F.g) (ρ t - 1 - supportQ F.gD F.f t) t ∧
        HasDerivAt (supportQ F.gD F.f)
          (σ (t + Real.pi / 2) - 1 + supportP F.fD F.g t) t := by
  dsimp only
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hf := hU.absolutelyContinuousOnInterval_angleSupport 0 (Real.pi / 2)
  have hg := hV.absolutelyContinuousOnInterval_angleSupport_shift 0 (Real.pi / 2) (Real.pi / 2)
  have hfD := hU.absolutelyContinuousOnInterval_closedSupportDerivative hρ hρ0 hρK 0 (Real.pi / 2) 0
  have hgD := hV.absolutelyContinuousOnInterval_closedSupportDerivative hσ hσ0 hσJ
    0 (Real.pi / 2) (Real.pi / 2)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 (Real.pi / 2) :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨(hfD.sub hg).add hc, (hgD.add hf).sub hc, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.ae_hasDerivAt_closedSupportDerivative hρ hρ0 hρK hL 0,
    hV.ae_hasDerivAt_closedSupportDerivative hσ hσ0 hσJ hL (Real.pi / 2)]
    with t ht hfDD hgDD
  have hdf := hU.hasDerivAt_shiftedSupport_of_open_density hρ hρ0 hρK hfirst
    (d := 0) (by simpa only [zero_add] using (Subset.rfl :
      Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2))) ht
  have hdg := hV.hasDerivAt_shiftedSupport_of_open_density hσ hσ0 hσJ hsecond
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩) ht
  simp only [add_zero] at hdf hfDD
  constructor
  · apply ((hfDD.sub hdg).add_const 1).congr_deriv
    dsimp only [supportQ, supportQuarterPair]
    ring
  · apply ((hgDD.add hdf).sub_const 1).congr_deriv
    dsimp only [supportP, supportQuarterPair]
    ring

theorem supportPoint_eq_of_frame {f fD : ℝ → ℝ} {p : Plane} {t : ℝ}
    (hf : f t = MovingSofaOptimality.dot p (MovingSofaOptimality.uvec t))
    (hfD : fD t = MovingSofaOptimality.dot p (MovingSofaOptimality.vvec t)) :
    Reference.supportPoint f fD t = p := by
  have hframe := MovingSofaOptimality.eq_dot_uvec_smul_add p t
  have hx := congrArg Prod.fst hframe
  have hy := congrArg Prod.snd hframe
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    MovingSofaOptimality.uvec, MovingSofaOptimality.vvec] at hx hy
  apply Prod.ext
  · change f t * Real.cos t - fD t * Real.sin t = p.1
    rw [hf, hfD]
    nlinarith only [hx]
  · change f t * Real.sin t + fD t * Real.cos t = p.2
    rw [hf, hfD]
    exact hy.symm

theorem companionSupportPoint_eq_shifted_supportPoint (g gD : ℝ → ℝ) (t : ℝ) :
    Reference.companionSupportPoint g gD t =
      Reference.supportPoint (fun s => g (s - Real.pi / 2))
        (fun s => gD (s - Real.pi / 2)) (t + Real.pi / 2) := by
  rw [companionSupportPoint_coordinates]
  simp only [Reference.supportPoint, add_sub_cancel_right,
    Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  apply Prod.ext <;> dsimp <;> ring

section PairGeometry

variable {U V : Set Plane} (hU : IsDownwardCap U) (hV : IsDownwardCap V)
  {ρ σ : ℝ → ℝ} {K J : ℝ}
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (hσ : Measurable σ) (hσ0 : ∀ t, 0 ≤ σ t) (hσJ : ∀ t, σ t ≤ J)
  (hfirst : (upperCurvature U).restrict (Ioo 0 (Real.pi / 2)) =
    (volume.restrict (Ioo 0 (Real.pi / 2))).withDensity (fun t => ENNReal.ofReal (ρ t)))
  (hsecond : (upperCurvature V).restrict (Ioo (Real.pi / 2) Real.pi) =
    (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
      (fun t => ENNReal.ofReal (σ t)))

local notation "F" => supportQuarterPair hU hV hρ hρ0 hρK hσ hσ0 hσJ hfirst hsecond

theorem supportQuarterPair_first_point {t : ℝ} (ht : t ∈ Ico 0 (Real.pi / 2)) :
    Reference.supportPoint (F).f (F).fD t = MovingSofaOptimality.vplus U t := by
  apply supportPoint_eq_of_frame
  · exact (MovingSofaOptimality.dot_vplus_uvec U t).symm
  · change closedSupportDerivative U ρ 0 t = supportTangent U t
    simpa only [add_zero] using hU.closedSupportDerivative_eq_supportTangent
      hρ hρ0 hρK hfirst (d := 0)
      (by simpa only [zero_add] using (Subset.rfl :
        Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2))) ht.1 ht.2

theorem supportQuarterPair_second_point {t : ℝ} (ht : t ∈ Ico 0 (Real.pi / 2)) :
    Reference.companionSupportPoint (F).g (F).gD t = MovingSofaOptimality.vplus V (t + Real.pi / 2) := by
  rw [companionSupportPoint_eq_shifted_supportPoint]
  apply supportPoint_eq_of_frame
  · simpa only [supportQuarterPair, add_sub_cancel_right] using
      (MovingSofaOptimality.dot_vplus_uvec V (t + Real.pi / 2)).symm
  · dsimp only [supportQuarterPair]
    rw [add_sub_cancel_right]
    exact hV.closedSupportDerivative_eq_supportTangent hσ hσ0 hσJ hsecond
      (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩) ht.1 ht.2

theorem supportQuarterPair_first_end :
    Reference.supportPoint (F).f (F).fD (Real.pi / 2) = MovingSofaOptimality.vminus U (Real.pi / 2) := by
  apply supportPoint_eq_of_frame
  · exact (MovingSofaOptimality.dot_vminus_uvec U (Real.pi / 2)).symm
  · simpa only [supportQuarterPair, add_zero] using
      hU.closedSupportDerivative_at_end hρ hρ0 hρK hfirst (d := 0)
        (by simpa only [zero_add] using (Subset.rfl :
          Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2)))

theorem supportQuarterPair_second_end :
    Reference.companionSupportPoint (F).g (F).gD (Real.pi / 2) = MovingSofaOptimality.vminus V Real.pi := by
  rw [companionSupportPoint_eq_shifted_supportPoint]
  apply supportPoint_eq_of_frame
  · simpa only [supportQuarterPair, add_sub_cancel_right,
      show Real.pi / 2 + Real.pi / 2 = Real.pi by ring] using
      (MovingSofaOptimality.dot_vminus_uvec V Real.pi).symm
  · dsimp only [supportQuarterPair]
    rw [add_sub_cancel_right]
    simpa only [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring] using
      hV.closedSupportDerivative_at_end hσ hσ0 hσJ hsecond (d := Real.pi / 2)
        (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩)

theorem supportQuarterPair_points_mem :
    (∀ t ∈ Icc 0 (Real.pi / 2), Reference.supportPoint (F).f (F).fD t ∈ U) ∧
      ∀ t ∈ Icc 0 (Real.pi / 2), Reference.companionSupportPoint (F).g (F).gD t ∈ V := by
  constructor
  · intro t ht
    rcases ht.2.eq_or_lt with rfl | htL
    · rw [supportQuarterPair_first_end]
      exact (MovingSofaOptimality.vminus_mem_edge hU.imported_isConvexBody _).1
    · rw [supportQuarterPair_first_point hU hV hρ hρ0 hρK hσ hσ0 hσJ hfirst hsecond ⟨ht.1, htL⟩]
      exact (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody _).1
  · intro t ht
    rcases ht.2.eq_or_lt with rfl | htL
    · rw [supportQuarterPair_second_end]
      exact (MovingSofaOptimality.vminus_mem_edge hV.imported_isConvexBody _).1
    · rw [supportQuarterPair_second_point hU hV hρ hρ0 hρK hσ hσ0 hσJ hfirst hsecond ⟨ht.1, htL⟩]
      exact (MovingSofaOptimality.vplus_mem_edge hV.imported_isConvexBody _).1

/-- All four support traces and all four derivative traces. In particular,
the two top traces are allowed to come from different faces and heights. -/
theorem supportQuarterPair_traces :
    (F).f 0 = horizontalRight U ∧ (F).g 0 = capHeight V ∧
      (F).f (Real.pi / 2) = capHeight U ∧ (F).g (Real.pi / 2) = -horizontalLeft V ∧
      (F).fD 0 = capRoof U (horizontalRight U) ∧
      (F).gD 0 = -(MovingSofaOptimality.vplus V (Real.pi / 2)).1 ∧
      (F).fD (Real.pi / 2) = -(MovingSofaOptimality.vminus U (Real.pi / 2)).1 ∧
      (F).gD (Real.pi / 2) = -capRoof V (horizontalLeft V) := by
  have hfDend := hU.closedSupportDerivative_at_end hρ hρ0 hρK hfirst (d := 0)
    (by simpa only [zero_add] using (Subset.rfl :
      Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2)))
  have hgDend := hV.closedSupportDerivative_at_end hσ hσ0 hσJ hsecond (d := Real.pi / 2)
    (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩)
  have hadd : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
  dsimp only [supportQuarterPair]
  refine ⟨imported_supp_zero U, ?_, imported_supp_pi_div_two U, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [zero_add] using imported_supp_pi_div_two V
  · simpa only [hadd] using hV.imported_supp_pi
  · simp only [closedSupportDerivative_zero, supportTangent, hU.axis_vplus_zero,
      MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_zero, Real.cos_zero, neg_zero,
      mul_zero, mul_one, zero_add]
  · simp only [closedSupportDerivative_zero, supportTangent, MovingSofaOptimality.dot, MovingSofaOptimality.vvec,
      Real.sin_pi_div_two, Real.cos_pi_div_two, mul_neg, mul_one, mul_zero, add_zero]
  · simpa only [add_zero, MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi_div_two,
      Real.cos_pi_div_two, mul_neg, mul_one, mul_zero, add_zero] using hfDend
  · simpa only [hadd, hV.axis_vminus_pi, MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi,
      Real.cos_pi, neg_zero, mul_zero, mul_neg, mul_one, zero_add] using hgDend

theorem supportQuarterPair_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (F).f 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (F).g 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (F).fD 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (F).gD 0 (Real.pi / 2) :=
  ⟨hU.absolutelyContinuousOnInterval_angleSupport _ _,
    hV.absolutelyContinuousOnInterval_angleSupport_shift _ _ _,
    hU.absolutelyContinuousOnInterval_closedSupportDerivative hρ hρ0 hρK _ _ _,
    hV.absolutelyContinuousOnInterval_closedSupportDerivative hσ hσ0 hσJ _ _ _⟩

theorem supportQuarterPair_ae_derivatives :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt (F).f ((F).fD t) t ∧ HasDerivAt (F).g ((F).gD t) t ∧
      HasDerivAt (F).fD (ρ t - (F).f t) t ∧
      HasDerivAt (F).gD (σ (t + Real.pi / 2) - (F).g t) t := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.ae_hasDerivAt_closedSupportDerivative hρ hρ0 hρK hL 0,
    hV.ae_hasDerivAt_closedSupportDerivative hσ hσ0 hσJ hL (Real.pi / 2)]
    with t ht hfDD hgDD
  have hdf := hU.hasDerivAt_shiftedSupport_of_open_density hρ hρ0 hρK hfirst
    (d := 0) (by simpa only [zero_add] using (Subset.rfl :
      Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2))) ht
  have hdg := hV.hasDerivAt_shiftedSupport_of_open_density hσ hσ0 hσJ hsecond
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩) ht
  exact ⟨by simpa only [add_zero] using hdf, hdg,
    by simpa only [add_zero] using hfDD, hgDD⟩

theorem supportQuarterPair_derivatives_on_closed :
    ∀ t ∈ Icc 0 (Real.pi / 2),
      HasDerivWithinAt (F).f ((F).fD t) (Icc 0 (Real.pi / 2)) t ∧
      HasDerivWithinAt (F).g ((F).gD t) (Icc 0 (Real.pi / 2)) t := by
  intro t ht
  constructor
  · simpa only [add_zero] using hU.hasDerivWithinAt_shiftedSupport_closed
      hρ hρ0 hρK hfirst (d := 0)
      (by simpa only [zero_add] using (Subset.rfl :
        Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2))) ht
  · exact hV.hasDerivWithinAt_shiftedSupport_closed hσ hσ0 hσJ hsecond
      (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩) ht

end PairGeometry

theorem horizontal_density_quarter_restrictions
    {U : Set Plane} {ρ : ℝ → ℝ}
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ((upperCurvature U).restrict (Ioo 0 (Real.pi / 2)) =
      (volume.restrict (Ioo 0 (Real.pi / 2))).withDensity (fun t => ENNReal.ofReal (ρ t))) ∧
    ((upperCurvature U).restrict (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity (fun t => ENNReal.ofReal (ρ t))) := by
  have hfirst : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCurvatureDomain 0 := by
    intro t ht
    simp only [regularCurvatureDomain, affineNormalAngle, Real.arctan_zero, zero_add,
      mem_sdiff, mem_Ioo, mem_insert_iff, mem_singleton_iff, or_self]
    exact ⟨⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩, ne_of_lt ht.2⟩
  have hsecond : Ioo (Real.pi / 2) Real.pi ⊆ regularCurvatureDomain 0 := by
    intro t ht
    simp only [regularCurvatureDomain, affineNormalAngle, Real.arctan_zero, zero_add,
      mem_sdiff, mem_Ioo, mem_insert_iff, mem_singleton_iff, or_self]
    exact ⟨⟨by linarith [ht.1, Real.pi_pos], ht.2⟩, ne_of_gt ht.1⟩
  constructor
  · have h := congrArg (fun ν : Measure ℝ => ν.restrict (Ioo 0 (Real.pi / 2))) heq
    simpa only [Measure.restrict_restrict_of_subset hfirst,
      Measure.restrict_withDensity measurableSet_Ioo] using h
  · have h := congrArg (fun ν : Measure ℝ => ν.restrict (Ioo (Real.pi / 2) Real.pi)) heq
    simpa only [Measure.restrict_restrict_of_subset hsecond,
      Measure.restrict_withDensity measurableSet_Ioo] using h

def horizontalSupportQuarterPair {U : Set Plane} (hU : IsDownwardCap U)
    {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    Analysis.QuarterPair :=
  supportQuarterPair hU hU hρ hρ0 hρK hρ hρ0 hρK
    (horizontal_density_quarter_restrictions heq).1 (horizontal_density_quarter_restrictions heq).2

theorem horizontalSupportQuarterPair_velocities
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    let F := horizontalSupportQuarterPair hU hρ hρ0 hρK heq
    supportP F.fD F.g t = -secondCornerVelocity U t ∧
      supportQ F.gD F.f t = firstCornerVelocity U t := by
  have hr := horizontal_density_quarter_restrictions heq
  have hfD := hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hr.1
    (d := 0) (by simpa only [zero_add] using (Subset.rfl :
      Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2))) ht.1.le ht.2
  have hgD := hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hr.2
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩) ht.1.le ht.2
  simp only [add_zero] at hfD
  dsimp only [horizontalSupportQuarterPair, supportQuarterPair, supportP, supportQ]
  rw [hfD, hgD]
  change (supportTangent U t - angleSupport U (t + Real.pi / 2) + 1 =
      -(angleSupport U (t + Real.pi / 2) - supportTangent U t - 1)) ∧
    (supportTangent U (t + Real.pi / 2) + angleSupport U t - 1 =
      angleSupport U t + supportTangent U (t + Real.pi / 2) - 1)
  constructor <;> ring

theorem IsFullCapMaximizer.horizontalSupportQuarterPair_traces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
    F.f 0 = horizontalRight U ∧ F.g 0 = 1 ∧
      F.f (Real.pi / 2) = 1 ∧ F.g (Real.pi / 2) = -horizontalLeft U ∧
      F.fD 0 = capRoof U (horizontalRight U) ∧
      F.gD 0 = -(horizontalLeft U + capWidth U / 4) ∧
      F.fD (Real.pi / 2) = -(horizontalRight U - capWidth U / 4) ∧
      F.gD (Real.pi / 2) = -capRoof U (horizontalLeft U) := by
  have htr := supportQuarterPair_traces hU.isCap hU.isCap hρ hρ0 hρK hρ hρ0 hρK
    (horizontal_density_quarter_restrictions heq).1 (horizontal_density_quarter_restrictions heq).2
  simpa only [horizontalSupportQuarterPair, hheight,
    hU.top_vplus_pi_div_two hheight hmiddle, hU.top_vminus_pi_div_two hheight hmiddle] using htr

theorem horizontalSupportQuarterPair_corner_calculus
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    let F := horizontalSupportQuarterPair hU hρ hρ0 hρK heq
    AbsolutelyContinuousOnInterval (supportP F.fD F.g) 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (supportQ F.gD F.f) 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        HasDerivAt (supportP F.fD F.g) (ρ t - 1 - supportQ F.gD F.f t) t ∧
        HasDerivAt (supportQ F.gD F.f)
          (ρ (t + Real.pi / 2) - 1 + supportP F.fD F.g t) t :=
  supportQuarterPair_corner_calculus hU hU hρ hρ0 hρK hρ hρ0 hρK
    (horizontal_density_quarter_restrictions heq).1 (horizontal_density_quarter_restrictions heq).2

end AmbidextrousSofa
