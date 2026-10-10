import AmbidextrousSofa.Measure.GraphIntegral
import AmbidextrousSofa.Analysis.RoofContinuity
import AmbidextrousSofa.Reference.Realization

/-!
# Support coordinates and actual cap area

The general integration identities retain all endpoint terms. They apply to
continuous first derivatives with integrable right second derivatives, hence
to the explicit reference even at its curvature switches. Actual cap area is
obtained from its roof and its realized boundary points, not postulated as a
support-energy certificate.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def innerCornerPoint (f g : ℝ → ℝ) (t : ℝ) : Plane :=
  ((f t - 1) * Real.cos t - (g t - 1) * Real.sin t,
    (f t - 1) * Real.sin t + (g t - 1) * Real.cos t)

def firstTangentPoint (f fD : ℝ → ℝ) (t : ℝ) : Plane :=
  Reference.supportPoint (fun s => f s - 1) fD t

def secondTangentPoint (g gD : ℝ → ℝ) (t : ℝ) : Plane :=
  Reference.companionSupportPoint (fun s => g s - 1) gD t

def supportP (fD g : ℝ → ℝ) (t : ℝ) : ℝ := fD t - g t + 1

def supportQ (gD f : ℝ → ℝ) (t : ℝ) : ℝ := gD t + f t - 1

def supportPointDX (f fDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(f t + fDD t) * Real.sin t

def supportPointDY (f fDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t + fDD t) * Real.cos t

def companionSupportPointDX (g gDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(g t + gDD t) * Real.cos t

def companionSupportPointDY (g gDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(g t + gDD t) * Real.sin t

theorem companionSupportPoint_coordinates (g gD : ℝ → ℝ) (t : ℝ) :
    Reference.companionSupportPoint g gD t =
      (-g t * Real.sin t - gD t * Real.cos t,
        g t * Real.cos t - gD t * Real.sin t) := by
  simp only [Reference.companionSupportPoint, Reference.supportPoint, rotate,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  apply Prod.ext <;> simp <;> ring

theorem hasDerivWithinAt_supportPoint_fst {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hfD : HasDerivWithinAt fD fDD (Ioi t) t) :
    HasDerivWithinAt (fun s => (Reference.supportPoint f fD s).1)
      (-(f t + fDD) * Real.sin t) (Ioi t) t := by
  unfold Reference.supportPoint
  apply ((hf.mul (Real.hasDerivAt_cos t).hasDerivWithinAt).sub
    (hfD.mul (Real.hasDerivAt_sin t).hasDerivWithinAt)).congr_deriv
  ring

theorem hasDerivWithinAt_supportPoint_snd {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hfD : HasDerivWithinAt fD fDD (Ioi t) t) :
    HasDerivWithinAt (fun s => (Reference.supportPoint f fD s).2)
      ((f t + fDD) * Real.cos t) (Ioi t) t := by
  unfold Reference.supportPoint
  apply ((hf.mul (Real.hasDerivAt_sin t).hasDerivWithinAt).add
    (hfD.mul (Real.hasDerivAt_cos t).hasDerivWithinAt)).congr_deriv
  ring

theorem hasDerivWithinAt_companionSupportPoint_fst {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivWithinAt g (gD t) (Ioi t) t)
    (hgD : HasDerivWithinAt gD gDD (Ioi t) t) :
    HasDerivWithinAt (fun s => (Reference.companionSupportPoint g gD s).1)
      (-(g t + gDD) * Real.cos t) (Ioi t) t := by
  have h := (hasDerivWithinAt_supportPoint_snd hg hgD).neg
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, neg_mul] using h

theorem hasDerivWithinAt_companionSupportPoint_snd {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivWithinAt g (gD t) (Ioi t) t)
    (hgD : HasDerivWithinAt gD gDD (Ioi t) t) :
    HasDerivWithinAt (fun s => (Reference.companionSupportPoint g gD s).2)
      (-(g t + gDD) * Real.sin t) (Ioi t) t := by
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, add_zero] using
    hasDerivWithinAt_supportPoint_fst hg hgD

theorem coordDet_supportPoint (f fD fDD : ℝ → ℝ) (t : ℝ) :
    coordDet (Reference.supportPoint f fD t)
      (supportPointDX f fDD t, supportPointDY f fDD t) = f t * (f t + fDD t) := by
  calc
    _ = f t * (f t + fDD t) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by
      unfold coordDet Reference.supportPoint supportPointDX supportPointDY
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem coordDet_companionSupportPoint (g gD gDD : ℝ → ℝ) (t : ℝ) :
    coordDet (Reference.companionSupportPoint g gD t)
      (companionSupportPointDX g gDD t, companionSupportPointDY g gDD t) =
      g t * (g t + gDD t) := by
  rw [companionSupportPoint_coordinates]
  calc
    _ = g t * (g t + gDD t) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by
      unfold coordDet companionSupportPointDX companionSupportPointDY
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- Integration by parts for the support density. All endpoint products are
explicit, including the products which encode the two vertical side faces. -/
theorem integral_support_density {a b : ℝ} {f fD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hfD : ContinuousOn fD (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hsecond : ∀ t ∈ Ioo a b, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume a b) :
    (∫ t in a..b, f t * (f t + fDD t)) =
      (∫ t in a..b, f t ^ 2 - fD t ^ 2) + f b * fD b - f a * fD a := by
  have hfu : ContinuousOn f (uIcc a b) := by simpa only [uIcc_of_le hab] using hf
  have hfDu : ContinuousOn fD (uIcc a b) := by simpa only [uIcc_of_le hab] using hfD
  have hfDi : IntervalIntegrable fD volume a b := hfDu.intervalIntegrable
  have henergy : IntervalIntegrable (fun t => f t ^ 2 - fD t ^ 2) volume a b :=
    ((hfu.pow 2).sub (hfDu.pow 2)).intervalIntegrable
  have hpartsI : IntervalIntegrable (fun t => fD t * fD t + f t * fDD t) volume a b :=
    (hfDi.mul_continuousOn hfDu).add (hfDD.continuousOn_mul hfu)
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right hfu hfDu
    (by simpa only [min_eq_left hab, max_eq_right hab] using hderiv)
    (by simpa only [min_eq_left hab, max_eq_right hab] using hsecond) hfDi hfDD
  calc
    _ = ∫ t in a..b, (f t ^ 2 - fD t ^ 2) +
        (fD t * fD t + f t * fDD t) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by rw [intervalIntegral.integral_add henergy hpartsI, hparts]; ring

/-- Combine the graph formula with the support-density identity. This is
the common analytic calculation for either upper support quarter. -/
theorem support_energy_graph_identity
    {a b : ℝ} {F X Y XD YD f fD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hXD : ∀ t ∈ Ioo a b, HasDerivWithinAt X (XD t) (Ioi t) t)
    (hYD : ∀ t ∈ Ioo a b, HasDerivWithinAt Y (YD t) (Ioi t) t)
    (hXDi : IntervalIntegrable XD volume a b) (hYDi : IntervalIntegrable YD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t)
    (hf : ContinuousOn f (Icc a b)) (hfD : ContinuousOn fD (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hsecond : ∀ t ∈ Ioo a b, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume a b)
    (hdet : ∀ t ∈ Ioo a b, coordDet (X t, Y t) (XD t, YD t) = f t * (f t + fDD t)) :
    2 * (∫ x in X a..X b, F x) =
      (X b * Y b - f b * fD b) - (X a * Y a - f a * fD a) -
        ∫ t in a..b, f t ^ 2 - fD t ^ 2 := by
  have hgraphInt := twice_integral_graph_parametrization hab hX hY hXD hYD hXDi hYDi hF hgraph
  have hdetInt : (∫ t in a..b, coordDet (X t, Y t) (XD t, YD t)) =
      ∫ t in a..b, f t * (f t + fDD t) :=
    intervalIntegral.integral_congr_Ioo_of_le hab hdet
  rw [hdetInt, integral_support_density hab hf hfD hderiv hsecond hfDD] at hgraphInt
  linarith

/-- A point attaining an upward support is the actual roof point over its
own abscissa. The sine condition makes the normal genuinely upward-facing. -/
theorem IsDownwardCap.capRoof_eq_of_support_eq {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) {θ : ℝ} (hsin : 0 < Real.sin θ)
    (hsupport : coordDot p (unitNormal θ) = support U (unitNormal θ)) :
    capRoof U p.1 = p.2 := by
  apply le_antisymm
  · have h := coordDot_le_support hU.isCompact
      (capRoof_mem hU.isCompact (mem_image_of_mem Prod.fst hp)) (unitNormal θ)
    rw [← hsupport] at h
    change p.1 * Real.cos θ + capRoof U p.1 * Real.sin θ ≤
      p.1 * Real.cos θ + p.2 * Real.sin θ at h
    apply (mul_le_mul_iff_left₀ hsin).mp
    linarith
  · exact le_capRoof hU.isCompact hp

/-- The two-quarter support-area formula for a realized cap with a horizontal
top face. The assumptions give actual boundary points, actual supports, and
actual face geometry. Vertical end faces are allowed; their endpoint terms
cancel instead of being omitted. Right second derivatives may jump. -/
theorem IsDownwardCap.volumeReal_eq_support_energy {U : Set Plane} (hU : IsDownwardCap U)
    {f g fD gD fDD gDD : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfD : Continuous fD) (hgD : Continuous gD)
    (hderivF : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt f (fD t) (Ioi t) t)
    (hderivG : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecondF : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hsecondG : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume 0 (Real.pi / 2))
    (hgDD : IntervalIntegrable gDD volume 0 (Real.pi / 2))
    (hFpoints : ∀ t ∈ Icc 0 (Real.pi / 2), Reference.supportPoint f fD t ∈ U)
    (hGpoints : ∀ t ∈ Icc 0 (Real.pi / 2), Reference.companionSupportPoint g gD t ∈ U)
    (hFsupport : ∀ t ∈ Ioo 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hGsupport : ∀ t ∈ Ioo 0 (Real.pi / 2),
      support U (unitNormal (t + Real.pi / 2)) = g t)
    (hleft : horizontalLeft U = -g (Real.pi / 2)) (hright : horizontalRight U = f 0)
    (hFtop : f (Real.pi / 2) = 1) (hGtop : g 0 = 1)
    (hfaceOrder : -gD 0 ≤ -fD (Real.pi / 2))
    (hface : ∀ x ∈ Icc (-gD 0) (-fD (Real.pi / 2)), capRoof U x = 1) :
    volume.real U = 1 / 2 * ∫ t in (0 : ℝ)..(Real.pi / 2),
      (f t ^ 2 - fD t ^ 2) + (g t ^ 2 - gD t ^ 2) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hFc : Continuous (Reference.supportPoint f fD) := by
    unfold Reference.supportPoint
    fun_prop
  have hGc : Continuous (Reference.companionSupportPoint g gD) := by
    unfold Reference.companionSupportPoint Reference.supportPoint rotate
    fun_prop
  have hFrho : IntervalIntegrable (fun t => f t + fDD t) volume 0 (Real.pi / 2) :=
    (hf.intervalIntegrable _ _).add hfDD
  have hGrho : IntervalIntegrable (fun t => g t + gDD t) volume 0 (Real.pi / 2) :=
    (hg.intervalIntegrable _ _).add hgDD
  have hFXDi : IntervalIntegrable (supportPointDX f fDD) volume 0 (Real.pi / 2) :=
    hFrho.neg.mul_continuousOn Real.continuous_sin.continuousOn
  have hFYDi : IntervalIntegrable (supportPointDY f fDD) volume 0 (Real.pi / 2) :=
    hFrho.mul_continuousOn Real.continuous_cos.continuousOn
  have hGXDi : IntervalIntegrable (companionSupportPointDX g gDD) volume 0 (Real.pi / 2) :=
    hGrho.neg.mul_continuousOn Real.continuous_cos.continuousOn
  have hGYDi : IntervalIntegrable (companionSupportPointDY g gDD) volume 0 (Real.pi / 2) :=
    hGrho.neg.mul_continuousOn Real.continuous_sin.continuousOn
  have hFgraph : ∀ t ∈ Ioo 0 (Real.pi / 2),
      capRoof U (Reference.supportPoint f fD t).1 = (Reference.supportPoint f fD t).2 := by
    intro t ht
    apply hU.capRoof_eq_of_support_eq (hFpoints t ⟨ht.1.le, ht.2.le⟩)
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]))
    rw [Reference.coordDot_supportPoint, Reference.supportProjection_self, hFsupport t ht]
  have hGgraph : ∀ t ∈ Ioo 0 (Real.pi / 2),
      capRoof U (Reference.companionSupportPoint g gD t).1 =
        (Reference.companionSupportPoint g gD t).2 := by
    intro t ht
    apply hU.capRoof_eq_of_support_eq (hGpoints t ⟨ht.1.le, ht.2.le⟩)
      (θ := t + Real.pi / 2)
    · rw [Real.sin_add_pi_div_two]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    · rw [Reference.coordDot_companionSupportPoint, add_sub_cancel_right,
        Reference.supportProjection_self, hGsupport t ht]
  have hFroof : ContinuousOn (capRoof U)
      ((fun t => (Reference.supportPoint f fD t).1) '' Icc 0 (Real.pi / 2)) := by
    apply hU.continuousOn_capRoof.mono
    rintro x ⟨t, ht, rfl⟩
    exact mem_image_of_mem Prod.fst (hFpoints t ht)
  have hGroof : ContinuousOn (capRoof U)
      ((fun t => (Reference.companionSupportPoint g gD t).1) '' Icc 0 (Real.pi / 2)) := by
    apply hU.continuousOn_capRoof.mono
    rintro x ⟨t, ht, rfl⟩
    exact mem_image_of_mem Prod.fst (hGpoints t ht)
  have hFenergy := support_energy_graph_identity hL hFc.fst.continuousOn hFc.snd.continuousOn
    (fun t ht => hasDerivWithinAt_supportPoint_fst (hderivF t ht) (hsecondF t ht))
    (fun t ht => hasDerivWithinAt_supportPoint_snd (hderivF t ht) (hsecondF t ht))
    hFXDi hFYDi hFroof hFgraph hf.continuousOn hfD.continuousOn hderivF hsecondF hfDD
    (fun t _ => coordDet_supportPoint f fD fDD t)
  have hGenergy := support_energy_graph_identity hL hGc.fst.continuousOn hGc.snd.continuousOn
    (fun t ht => hasDerivWithinAt_companionSupportPoint_fst (hderivG t ht) (hsecondG t ht))
    (fun t ht => hasDerivWithinAt_companionSupportPoint_snd (hderivG t ht) (hsecondG t ht))
    hGXDi hGYDi hGroof hGgraph hg.continuousOn hgD.continuousOn hderivG hsecondG hgDD
    (fun t _ => coordDet_companionSupportPoint g gD gDD t)
  simp only [Reference.supportPoint, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero,
    zero_sub, hFtop, one_mul] at hFenergy
  simp only [companionSupportPoint_coordinates, Real.cos_zero, Real.sin_zero,
    Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_mul, zero_add,
    add_zero, sub_zero, zero_sub, hGtop, one_mul, neg_mul] at hGenergy
  have harea := hU.volumeReal_eq_wing_integrals hleft hright hfaceOrder hface
  have hFi : IntervalIntegrable (fun t => f t ^ 2 - fD t ^ 2) volume 0 (Real.pi / 2) :=
    ((hf.pow 2).sub (hfD.pow 2)).intervalIntegrable _ _
  have hGi : IntervalIntegrable (fun t => g t ^ 2 - gD t ^ 2) volume 0 (Real.pi / 2) :=
    ((hg.pow 2).sub (hgD.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hFi hGi]
  nlinarith

end AmbidextrousSofa
