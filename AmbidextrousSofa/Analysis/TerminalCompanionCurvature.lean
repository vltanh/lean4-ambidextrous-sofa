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
top atom is outside this interval; no smoothness of the support or
absolute-continuity certificate is assumed.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem setIntegral_eq_density_mul_of_restrict_withDensity
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S s : Set ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ r, 0 ≤ ρ r)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun r => ENNReal.ofReal (ρ r)))
    (hs : MeasurableSet s) (hsub : s ⊆ S) (f : ℝ → ℝ) :
    (∫ r in s, f r ∂μ) = ∫ r in s, ρ r * f r := by
  have hrestrict := congrArg (fun ν : Measure ℝ => ν.restrict s) heq
  rw [Measure.restrict_restrict_of_subset hsub, restrict_withDensity hs,
    Measure.restrict_restrict_of_subset hsub] at hrestrict
  change (∫ r, f r ∂μ.restrict s) = ∫ r, ρ r * f r ∂volume.restrict s
  rw [hrestrict]
  have h := integral_withDensity_eq_integral_toReal_smul
    (μ := volume.restrict s) hρ.ennreal_ofReal
    (Eventually.of_forall (fun _r => ENNReal.ofReal_lt_top)) f
  simpa only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul] using h

def shiftedCompanionX (U : Set Plane) (t : ℝ) : ℝ :=
  (MovingSofaOptimality.vplus U (t + Real.pi / 2)).1 + Real.sin t

def shiftedCompanionY (U : Set Plane) (t : ℝ) : ℝ :=
  (MovingSofaOptimality.vplus U (t + Real.pi / 2)).2 - Real.cos t

@[simp] theorem shiftedCompanionX_zero (U : Set Plane) :
    shiftedCompanionX U 0 = (MovingSofaOptimality.vplus U (Real.pi / 2)).1 := by
  simp [shiftedCompanionX]

@[simp] theorem shiftedCompanionY_zero (U : Set Plane) :
    shiftedCompanionY U 0 = (MovingSofaOptimality.vplus U (Real.pi / 2)).2 - 1 := by
  simp [shiftedCompanionY]

/-- The right-continuous boundary representative leaves the top face
at its literal left endpoint. Its height is the cap height. -/
theorem top_vplus_snd_eq_capHeight (U : Set Plane) :
    (MovingSofaOptimality.vplus U (Real.pi / 2)).2 = capHeight U := by
  have h : coordDot (MovingSofaOptimality.vplus U (Real.pi / 2)) (unitNormal (Real.pi / 2)) =
      angleSupport U (Real.pi / 2) := MovingSofaOptimality.dot_vplus_uvec U (Real.pi / 2)
  simpa only [coordDot, unitNormal, angleSupport, capHeight,
    Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add] using h

/-- Distance of the actual left top endpoint from the left projection
endpoint. In the centered proper-terminal notation this is `C - T_L`. -/
def companionInitialOffset (U : Set Plane) : ℝ :=
  (MovingSofaOptimality.vplus U (Real.pi / 2)).1 - horizontalLeft U

def companionInitialDeficit (U : Set Plane) : ℝ := 1 - capHeight U

theorem IsDownwardCap.companionInitialDeficit_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) : 0 ≤ companionInitialDeficit U :=
  sub_nonneg.mpr hU.capHeight_le_one

theorem shiftedCompanion_initial_data (U : Set Plane) :
    shiftedCompanionX U 0 = horizontalLeft U + companionInitialOffset U ∧
      shiftedCompanionY U 0 = -companionInitialDeficit U := by
  rw [shiftedCompanionX_zero, shiftedCompanionY_zero, top_vplus_snd_eq_capHeight]
  unfold companionInitialOffset companionInitialDeficit
  constructor <;> ring

/-- The actual companion support has the required right derivative at
zero, even when its initial top face has a nonzero atom. -/
theorem IsDownwardCap.hasDerivWithinAt_companionSupport_zero
    {U : Set Plane} (hU : IsDownwardCap U) :
    HasDerivWithinAt (fun t => angleSupport U (t + Real.pi / 2))
      (-(MovingSofaOptimality.vplus U (Real.pi / 2)).1) (Ici 0) 0 := by
  have houter := hU.angleSupport_right_deriv (0 + Real.pi / 2)
  have hinner : HasDerivWithinAt (fun t : ℝ => t + Real.pi / 2) 1 (Ici 0) 0 :=
    ((hasDerivAt_id (0 : ℝ)).add_const (Real.pi / 2)).hasDerivWithinAt
  have h := houter.comp 0 hinner (fun t ht => by
    simp only [mem_Ici] at ht ⊢
    linarith only [ht])
  simpa only [zero_add, mul_one, MovingSofaOptimality.dot, MovingSofaOptimality.vvec,
    Real.sin_pi_div_two, Real.cos_pi_div_two, mul_neg, mul_zero, add_zero, coordDot,
    Function.comp_def] using h

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
  have hvec := MovingSofaOptimality.vplus_sub_vplus hU.imported_isConvexBody
    (add_le_add_left hab (Real.pi / 2))
  have hic : IntegrableOn MovingSofaOptimality.vvec
      (Icc (a + Real.pi / 2) (b + Real.pi / 2)) (MovingSofaOptimality.sigma U) :=
    MovingSofaOptimality.continuous_vvec.integrableOn_Icc
  have hi := hic.mono_set Ioc_subset_Icc_self
  have hx := congrArg Prod.fst hvec
  have hy := congrArg Prod.snd hvec
  rw [fst_integral hi] at hx
  rw [snd_integral hi] at hy
  change (MovingSofaOptimality.vplus U (b + Real.pi / 2)).1 -
      (MovingSofaOptimality.vplus U (a + Real.pi / 2)).1 =
        ∫ r in Ioc (a + Real.pi / 2) (b + Real.pi / 2), -Real.sin r ∂upperCurvature U at hx
  change (MovingSofaOptimality.vplus U (b + Real.pi / 2)).2 -
      (MovingSofaOptimality.vplus U (a + Real.pi / 2)).2 =
        ∫ r in Ioc (a + Real.pi / 2) (b + Real.pi / 2), Real.cos r ∂upperCurvature U at hy
  rw [setIntegral_eq_density_mul_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub,
    ← intervalIntegral.integral_of_le (add_le_add_left hab (Real.pi / 2)),
    ← intervalIntegral.integral_comp_add_right (fun r => ρ r * (-Real.sin r)) (Real.pi / 2)] at hx
  rw [setIntegral_eq_density_mul_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub,
    ← intervalIntegral.integral_of_le (add_le_add_left hab (Real.pi / 2)),
    ← intervalIntegral.integral_comp_add_right (fun r => ρ r * Real.cos r) (Real.pi / 2)] at hy
  simp only [Real.sin_add_pi_div_two, mul_neg, intervalIntegral.integral_neg] at hx
  simp only [Real.cos_add_pi_div_two, mul_neg, intervalIntegral.integral_neg] at hy
  have hρi : IntervalIntegrable (fun r => ρ (r + Real.pi / 2)) volume a b :=
    intervalIntegrable_bounded_real_density (hρ.comp (measurable_id.add_const _))
      (fun r => hρ0 _) (fun r => hρC _) a b
  have hX : (∫ r in a..b, (1 - ρ (r + Real.pi / 2)) * Real.cos r) =
      Real.sin b - Real.sin a - ∫ r in a..b, ρ (r + Real.pi / 2) * Real.cos r := by
    calc
      _ = ∫ r in a..b, Real.cos r - ρ (r + Real.pi / 2) * Real.cos r := by
        apply intervalIntegral.integral_congr
        intro r _hr
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (Real.continuous_cos.intervalIntegrable a b)
          (hρi.mul_continuousOn Real.continuous_cos.continuousOn), integral_cos]
  have hY : (∫ r in a..b, (1 - ρ (r + Real.pi / 2)) * Real.sin r) =
      Real.cos a - Real.cos b - ∫ r in a..b, ρ (r + Real.pi / 2) * Real.sin r := by
    calc
      _ = ∫ r in a..b, Real.sin r - ρ (r + Real.pi / 2) * Real.sin r := by
        apply intervalIntegral.integral_congr
        intro r _hr
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (Real.continuous_sin.intervalIntegrable a b)
          (hρi.mul_continuousOn Real.continuous_sin.continuousOn), integral_sin]
  unfold shiftedCompanionX shiftedCompanionY
  constructor <;> linarith only [hx, hy, hX, hY]

/-- The two moments start from the actual top endpoint. In particular,
the initial height deficit is derived from the cap itself. The initial
top atom does not occur in either integral. -/
theorem IsDownwardCap.shiftedCompanion_eq_initial_add_integral_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ r, 0 ≤ ρ r) (hρC : ∀ r, ρ r ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun r => ENNReal.ofReal (ρ r)))
    (ht : 0 ≤ t) (hsub : Ioc (Real.pi / 2) (t + Real.pi / 2) ⊆ S) :
    shiftedCompanionX U t - (horizontalLeft U + companionInitialOffset U) =
        (∫ r in 0..t, (1 - ρ (r + Real.pi / 2)) * Real.cos r) ∧
      shiftedCompanionY U t + companionInitialDeficit U =
        ∫ r in 0..t, (1 - ρ (r + Real.pi / 2)) * Real.sin r := by
  have h := hU.shiftedCompanion_sub_eq_integral_of_density hρ hρ0 hρC heq ht
    (by simpa only [zero_add] using hsub)
  rw [(shiftedCompanion_initial_data U).1, (shiftedCompanion_initial_data U).2] at h
  simpa only [sub_neg_eq_add] using h

end AmbidextrousSofa
