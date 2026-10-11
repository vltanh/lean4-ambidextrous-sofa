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

theorem IsDownwardCap.continuous_closedSupportDerivative
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) (d : ℝ) :
    Continuous (closedSupportDerivative U ρ d) :=
  continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => hU.intervalIntegrable_shift_density hρ hρ0 hρK a b d) 0)

theorem IsDownwardCap.absolutelyContinuousOnInterval_closedSupportDerivative
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (a b d : ℝ) :
    AbsolutelyContinuousOnInterval (closedSupportDerivative U ρ d) a b := by
  have hi := hU.intervalIntegrable_shift_density hρ hρ0 hρK
  refine absolutelyContinuousOnInterval_of_integral_sub (hi a b d) fun x _ => ?_
  rw [closedSupportDerivative, closedSupportDerivative, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hi 0 x d) (hi 0 a d)]

theorem IsDownwardCap.ae_hasDerivAt_closedSupportDerivative
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) (d : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (closedSupportDerivative U ρ d)
        (ρ (t + d) - angleSupport U (t + d)) t := by
  have hi := hU.intervalIntegrable_shift_density hρ hρ0 hρK
    (min 0 a) (max 0 b) d
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae hi.ae_hasDerivAt_integral] with t ht hdt
  rw [uIcc_of_le ((min_le_left 0 a).trans (le_max_left 0 b))] at hdt
  exact (hdt ⟨(min_le_right _ _).trans ht.1.le, ht.2.le.trans (le_max_right _ _)⟩ 0
    ⟨min_le_left _ _, le_max_left _ _⟩).const_add (supportTangent U d)

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
  · simp
  simp only [supportTangent, dot_vplus_vvec_sub hU.imported_isConvexBody hab,
    angleSupport_eq_imported_supp]
  rw [intervalIntegral.integral_sub (intervalIntegrable_bounded_real_density hρ hρ0 hρK a b)
    (hU.imported_isConvexBody.continuous_supp.intervalIntegrable a b),
    intervalIntegral.integral_of_le (f := ρ) hab.le,
    ← measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub]
  rfl

theorem IsDownwardCap.closedSupportDerivative_eq_supportTangent
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K d t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo d (d + Real.pi / 2) ⊆ S)
    (ht0 : 0 ≤ t) (htL : t < Real.pi / 2) :
    closedSupportDerivative U ρ d t = supportTangent U (t + d) := by
  have hid := hU.supportTangent_sub_eq_integral_of_density_Ioc hρ hρ0 hρK heq
    (a := d) (b := t + d) (by linarith) fun s hs => hsub ⟨hs.1, by linarith [hs.2]⟩
  rw [closedSupportDerivative,
    intervalIntegral.integral_comp_add_right (fun s => ρ s - angleSupport U s), zero_add]
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
  have hlim := (MovingSofaOptimality.continuous_dot_pair.tendsto _).comp
    (((MovingSofaOptimality.tendsto_vplus_left hU.imported_isConvexBody (Real.pi / 2 + d)).comp
      map_add_right_nhdsLT.le).prodMk_nhds
      (((MovingSofaOptimality.continuous_vvec.comp (continuous_id.add_const d)).tendsto _).mono_left
        nhdsWithin_le_nhds))
  refine tendsto_nhds_unique (((hU.continuous_closedSupportDerivative hρ hρ0 hρK d).tendsto
    _).mono_left nhdsWithin_le_nhds) (hlim.congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT Real.pi_div_two_pos] with t ht
  exact (hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq hsub ht.1.le ht.2).symm

theorem IsDownwardCap.hasDerivAt_shiftedSupport_of_open_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K d t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo d (d + Real.pi / 2) ⊆ S) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun s => angleSupport U (s + d)) (closedSupportDerivative U ρ d t) t := by
  rw [hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq hsub ht.1.le ht.2]
  exact (hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρK heq (a := d + t / 2)
    (b := d + (t + Real.pi / 2) / 2)
    (fun s hs => hsub ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_add_const t d

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
  refine (((hU.continuous_closedSupportDerivative hρ hρ0 hρK d).integral_hasStrictDerivAt
    0 t).hasDerivAt.const_add (angleSupport U d)).hasDerivWithinAt.congr_of_mem
    (fun s hs => ?_) ht
  have h := hU.angleSupport_shift_sub_eq_integral 0 s d
  rw [zero_add, ← intervalIntegral.integral_congr_Ioo_of_le hs.1 fun r hr =>
    hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq hsub hr.1.le
      (hr.2.trans_le hs.2)] at h
  linarith

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

theorem supportPoint_eq_of_frame {f fD : ℝ → ℝ} {p : Plane} {t : ℝ}
    (hf : f t = MovingSofaOptimality.dot p (MovingSofaOptimality.uvec t))
    (hfD : fD t = MovingSofaOptimality.dot p (MovingSofaOptimality.vvec t)) :
    Reference.supportPoint f fD t = p := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [MovingSofaOptimality.dot, MovingSofaOptimality.uvec,
    MovingSofaOptimality.vvec] at hf hfD
  ext <;> simp only [Reference.supportPoint, hf, hfD]
  · linear_combination p.1 * h
  · linear_combination p.2 * h

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

theorem supportQuarterPair_points_mem :
    (∀ t ∈ Icc 0 (Real.pi / 2), Reference.supportPoint (F).f (F).fD t ∈ U) ∧
      ∀ t ∈ Icc 0 (Real.pi / 2), Reference.companionSupportPoint (F).g (F).gD t ∈ V := by
  have hK := hU.imported_isConvexBody
  have hL := hV.imported_isConvexBody
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩ <;> rcases ht.2.eq_or_lt with rfl | htL
  · convert (MovingSofaOptimality.vminus_mem_edge hK (Real.pi / 2)).1 using 1
    refine supportPoint_eq_of_frame (MovingSofaOptimality.dot_vminus_uvec U _).symm ?_
    simpa only [supportQuarterPair, add_zero] using
      hU.closedSupportDerivative_at_end hρ hρ0 hρK hfirst (d := 0) (by simp)
  · convert (MovingSofaOptimality.vplus_mem_edge hK t).1 using 1
    refine supportPoint_eq_of_frame (MovingSofaOptimality.dot_vplus_uvec U t).symm ?_
    simpa only [supportQuarterPair, supportTangent, add_zero] using
      hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hfirst (d := 0) (by simp) ht.1 htL
  · convert (MovingSofaOptimality.vminus_mem_edge hL Real.pi).1 using 1
    rw [companionSupportPoint_eq_shifted_supportPoint]
    refine supportPoint_eq_of_frame ?_ ?_
    · simpa only [supportQuarterPair, add_sub_cancel_right, sub_add_cancel, add_halves,
        angleSupport_eq_imported_supp] using (MovingSofaOptimality.dot_vminus_uvec V Real.pi).symm
    · simpa only [supportQuarterPair, add_sub_cancel_right, add_halves, sub_half] using
        hV.closedSupportDerivative_at_end hσ hσ0 hσJ hsecond (d := Real.pi / 2) (by simp)
  · convert (MovingSofaOptimality.vplus_mem_edge hL (t + Real.pi / 2)).1 using 1
    rw [companionSupportPoint_eq_shifted_supportPoint]
    refine supportPoint_eq_of_frame ?_ ?_
    · simpa only [supportQuarterPair, add_sub_cancel_right, angleSupport_eq_imported_supp] using
        (MovingSofaOptimality.dot_vplus_uvec V (t + Real.pi / 2)).symm
    · simpa only [supportQuarterPair, add_sub_cancel_right, supportTangent] using
        hV.closedSupportDerivative_eq_supportTangent hσ hσ0 hσJ hsecond (d := Real.pi / 2)
          (by simp) ht.1 htL

/-- All four support traces and all four derivative traces. In particular,
the two top traces are allowed to come from different faces and heights. -/
theorem supportQuarterPair_traces :
    (F).f 0 = horizontalRight U ∧ (F).g 0 = capHeight V ∧
      (F).f (Real.pi / 2) = capHeight U ∧ (F).g (Real.pi / 2) = -horizontalLeft V ∧
      (F).fD 0 = capRoof U (horizontalRight U) ∧
      (F).gD 0 = -(MovingSofaOptimality.vplus V (Real.pi / 2)).1 ∧
      (F).fD (Real.pi / 2) = -(MovingSofaOptimality.vminus U (Real.pi / 2)).1 ∧
      (F).gD (Real.pi / 2) = -capRoof V (horizontalLeft V) := by
  have hfDend := hU.closedSupportDerivative_at_end hρ hρ0 hρK hfirst (d := 0) (by simp)
  have hgDend := hV.closedSupportDerivative_at_end hσ hσ0 hσJ hsecond (d := Real.pi / 2)
    (by simp)
  dsimp only [supportQuarterPair]
  refine ⟨imported_supp_zero U, ?_, imported_supp_pi_div_two U, ?_, ?_, ?_, hfDend.trans ?_,
    hgDend.trans ?_⟩ <;>
    simp [closedSupportDerivative, supportTangent, hU.axis_vplus_zero, hV.axis_vminus_pi,
      MovingSofaOptimality.dot, MovingSofaOptimality.vvec, angleSupport_eq_imported_supp,
      imported_supp_pi_div_two, hV.imported_supp_pi]

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
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.ae_hasDerivAt_closedSupportDerivative hρ hρ0 hρK 0,
    hV.ae_hasDerivAt_closedSupportDerivative hσ hσ0 hσJ (Real.pi / 2)]
    with t ht hfDD hgDD
  have hdf := hU.hasDerivAt_shiftedSupport_of_open_density hρ hρ0 hρK hfirst (d := 0) (by simp) ht
  simp only [add_zero] at hdf hfDD
  exact ⟨hdf, hV.hasDerivAt_shiftedSupport_of_open_density hσ hσ0 hσJ hsecond
    (d := Real.pi / 2) (by simp) ht, hfDD, hgDD⟩

theorem supportQuarterPair_derivatives_on_closed :
    ∀ t ∈ Icc 0 (Real.pi / 2),
      HasDerivWithinAt (F).f ((F).fD t) (Icc 0 (Real.pi / 2)) t ∧
      HasDerivWithinAt (F).g ((F).gD t) (Icc 0 (Real.pi / 2)) t := fun t ht =>
  ⟨by simpa only [supportQuarterPair, add_zero] using
        hU.hasDerivWithinAt_shiftedSupport_closed hρ hρ0 hρK hfirst (d := 0) (by simp) ht,
    hV.hasDerivWithinAt_shiftedSupport_closed hσ hσ0 hσJ hsecond (d := Real.pi / 2) (by simp) ht⟩

end PairGeometry

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
  intro F
  obtain ⟨hf, hg, hfD, hgD⟩ :=
    supportQuarterPair_absolutelyContinuous hU hV hρ hρ0 hρK hσ hσ0 hσJ hfirst hsecond
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 (Real.pi / 2) :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨(hfD.sub hg).add hc, (hgD.add hf).sub hc, ?_⟩
  filter_upwards [supportQuarterPair_ae_derivatives hU hV hρ hρ0 hρK hσ hσ0 hσJ hfirst hsecond]
    with t ⟨hdf, hdg, hdfD, hdgD⟩
  exact ⟨((hdfD.sub hdg).add_const 1).congr_deriv (by rw [supportQ]; ring),
    ((hdgD.add hdf).sub_const 1).congr_deriv (by rw [supportP]; ring)⟩

theorem horizontal_density_quarter_restrictions
    {U : Set Plane} {ρ : ℝ → ℝ}
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ((upperCurvature U).restrict (Ioo 0 (Real.pi / 2)) =
      (volume.restrict (Ioo 0 (Real.pi / 2))).withDensity (fun t => ENNReal.ofReal (ρ t))) ∧
    ((upperCurvature U).restrict (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity (fun t => ENNReal.ofReal (ρ t))) := by
  have key (s : Set ℝ) (hs : s ⊆ Ioo 0 Real.pi \ {Real.pi / 2}) (hm : MeasurableSet s) :
      (upperCurvature U).restrict s =
        (volume.restrict s).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
    have hs' : s ⊆ regularCurvatureDomain 0 := by
      simpa [regularCurvatureDomain, affineNormalAngle] using hs
    simpa only [Measure.restrict_restrict_of_subset hs', restrict_withDensity hm] using
      congrArg (fun ν : Measure ℝ => ν.restrict s) heq
  exact ⟨key _ (fun t ht => ⟨⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩, ht.2.ne⟩) measurableSet_Ioo,
    key _ (fun t ht => ⟨⟨by linarith [ht.1, Real.pi_pos], ht.2⟩, ht.1.ne'⟩) measurableSet_Ioo⟩

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
  simp only [horizontalSupportQuarterPair, supportQuarterPair, supportP, supportQ,
    hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hr.1 (d := 0) (by simp) ht.1.le ht.2,
    hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hr.2 (d := Real.pi / 2) (by simp)
      ht.1.le ht.2, secondCornerVelocity, firstCornerVelocity, angleSupport_eq_imported_supp,
    supportTangent, add_zero]
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
