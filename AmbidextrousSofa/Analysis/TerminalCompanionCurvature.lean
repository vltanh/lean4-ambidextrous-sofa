module

public import AmbidextrousSofa.Analysis.TerminalCompanionMoment
public import AmbidextrousSofa.Analysis.TerminalCompanionLocalization
public import AmbidextrousSofa.Analysis.SupportDensityCalculus

@[expose] public section

/-!
# Actual companion-coordinate moments from the curvature measure

The boundary Stieltjes integral gives the difference of the actual
supporting endpoints. Substituting a literal density on the half-open
angle interval proves both companion-coordinate moments directly. The
top atom is outside this interval. The arc starts at the left endpoint
of the top face, at the cap height.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def shiftedCompanionX (U : Set Plane) (t : ℝ) : ℝ :=
  (MovingSofaOptimality.vplus U (t + Real.pi / 2)).1 + Real.sin t

def shiftedCompanionY (U : Set Plane) (t : ℝ) : ℝ :=
  (MovingSofaOptimality.vplus U (t + Real.pi / 2)).2 - Real.cos t

/-- The left endpoint of the top face, where the companion arc starts, is at the cap height. -/
theorem top_vplus_snd_eq_capHeight (U : Set Plane) :
    (MovingSofaOptimality.vplus U (Real.pi / 2)).2 = capHeight U := by
  rw [← MovingSofaOptimality.dot_uvec_pi_div_two, MovingSofaOptimality.dot_vplus_uvec,
    imported_supp_pi_div_two]

/-- Distance of the actual left top endpoint from the left projection
endpoint. In the centered proper-terminal notation this is `C - T_L`. -/
def companionInitialOffset (U : Set Plane) : ℝ :=
  (MovingSofaOptimality.vplus U (Real.pi / 2)).1 - horizontalLeft U

def companionInitialDeficit (U : Set Plane) : ℝ := 1 - capHeight U

theorem IsDownwardCap.companionInitialDeficit_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) : 0 ≤ companionInitialDeficit U :=
  sub_nonneg.mpr hU.capHeight_le_one

/-- The actual companion support has the required right derivative at
zero, even when its initial top face has a nonzero atom. -/
theorem IsDownwardCap.hasDerivWithinAt_companionSupport_zero
    {U : Set Plane} (hU : IsDownwardCap U) :
    HasDerivWithinAt (fun t => angleSupport U (t + Real.pi / 2))
      (-(MovingSofaOptimality.vplus U (Real.pi / 2)).1) (Ici 0) 0 := by
  have h := (hU.angleSupport_right_deriv (0 + Real.pi / 2)).comp 0
    (((hasDerivAt_id' (0 : ℝ)).add_const (Real.pi / 2)).hasDerivWithinAt (s := Ici 0))
    (fun t ht => by rw [mem_Ici] at ht ⊢; linarith)
  simpa only [zero_add, mul_one, Function.comp_def, coordDot, MovingSofaOptimality.vvec,
    Real.sin_pi_div_two, Real.cos_pi_div_two, mul_neg, mul_zero, add_zero] using h

/-- Both literal endpoint-coordinate moments. The density domain only
needs to contain the half-open arc, so the initial supporting atom is
retained without entering either moment. -/
theorem IsDownwardCap.shiftedCompanion_sub_eq_integral_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ r, 0 ≤ ρ r) (hρC : ∀ r, ρ r ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun r => ENNReal.ofReal (ρ r)))
    (hab : a ≤ b) (hsub : Ioc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    shiftedCompanionX U b - shiftedCompanionX U a =
        (∫ r in a..b, (1 - ρ (r + Real.pi / 2)) * Real.cos r) ∧
      shiftedCompanionY U b - shiftedCompanionY U a =
        ∫ r in a..b, (1 - ρ (r + Real.pi / 2)) * Real.sin r := by
  have hab' : a + Real.pi / 2 ≤ b + Real.pi / 2 := by linarith
  have hvec : MovingSofaOptimality.vplus U (b + Real.pi / 2) -
      MovingSofaOptimality.vplus U (a + Real.pi / 2) =
        ∫ r in Ioc (a + Real.pi / 2) (b + Real.pi / 2), MovingSofaOptimality.vvec r
          ∂upperCurvature U :=
    MovingSofaOptimality.vplus_sub_vplus hU.imported_isConvexBody hab'
  have hi : IntegrableOn MovingSofaOptimality.vvec (Ioc (a + Real.pi / 2) (b + Real.pi / 2))
      (upperCurvature U) :=
    MovingSofaOptimality.continuous_vvec.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have key (g : ℝ → ℝ) : ∫ r in Ioc (a + Real.pi / 2) (b + Real.pi / 2), g r ∂upperCurvature U =
      ∫ r in a..b, ρ (r + Real.pi / 2) * g (r + Real.pi / 2) := by
    rw [setIntegral_eq_density_mul_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub,
      ← intervalIntegral.integral_of_le hab',
      intervalIntegral.integral_comp_add_right (fun r => ρ r * g r)]
  have hρi : IntervalIntegrable (fun r => ρ (r + Real.pi / 2)) volume a b :=
    intervalIntegrable_bounded_real_density (hρ.comp (measurable_id.add_const _))
      (fun _ => hρ0 _) (fun _ => hρC _) a b
  have hx := congrArg Prod.fst hvec
  have hy := congrArg Prod.snd hvec
  rw [fst_integral hi, key] at hx
  rw [snd_integral hi, key] at hy
  simp only [Prod.fst_sub, Prod.snd_sub, MovingSofaOptimality.vvec, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, mul_neg, intervalIntegral.integral_neg] at hx hy
  simp_rw [sub_mul, one_mul]
  rw [intervalIntegral.integral_sub (Real.continuous_cos.intervalIntegrable a b)
      (hρi.mul_continuousOn Real.continuous_cos.continuousOn), integral_cos,
    intervalIntegral.integral_sub (Real.continuous_sin.intervalIntegrable a b)
      (hρi.mul_continuousOn Real.continuous_sin.continuousOn), integral_sin]
  unfold shiftedCompanionX shiftedCompanionY
  constructor <;> linarith

end AmbidextrousSofa
