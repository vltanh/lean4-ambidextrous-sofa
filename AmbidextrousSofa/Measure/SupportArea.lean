module

public import AmbidextrousSofa.Measure.GraphIntegral
public import AmbidextrousSofa.Analysis.RoofContinuity
public import AmbidextrousSofa.Reference.Realization

@[expose] public section

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

def supportPointDX (f fDD : ℝ → ℝ) (t : ℝ) : ℝ := -(f t + fDD t) * Real.sin t

def supportPointDY (f fDD : ℝ → ℝ) (t : ℝ) : ℝ := (f t + fDD t) * Real.cos t

def companionSupportPointDX (g gDD : ℝ → ℝ) (t : ℝ) : ℝ := -(g t + gDD t) * Real.cos t

def companionSupportPointDY (g gDD : ℝ → ℝ) (t : ℝ) : ℝ := -(g t + gDD t) * Real.sin t

theorem companionSupportPoint_coordinates (g gD : ℝ → ℝ) (t : ℝ) :
    Reference.companionSupportPoint g gD t =
      (-g t * Real.sin t - gD t * Real.cos t,
        g t * Real.cos t - gD t * Real.sin t) := by
  simp [Reference.companionSupportPoint, Reference.supportPoint, rotate]
  ring

theorem hasDerivWithinAt_supportPoint_fst {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hfD : HasDerivWithinAt fD fDD (Ioi t) t) :
    HasDerivWithinAt (fun s => (Reference.supportPoint f fD s).1)
      (-(f t + fDD) * Real.sin t) (Ioi t) t :=
  ((hf.mul (Real.hasDerivAt_cos t).hasDerivWithinAt).sub
    (hfD.mul (Real.hasDerivAt_sin t).hasDerivWithinAt)).congr_deriv (by ring)

theorem hasDerivWithinAt_supportPoint_snd {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hfD : HasDerivWithinAt fD fDD (Ioi t) t) :
    HasDerivWithinAt (fun s => (Reference.supportPoint f fD s).2)
      ((f t + fDD) * Real.cos t) (Ioi t) t :=
  ((hf.mul (Real.hasDerivAt_sin t).hasDerivWithinAt).add
    (hfD.mul (Real.hasDerivAt_cos t).hasDerivWithinAt)).congr_deriv (by ring)

theorem hasDerivWithinAt_companionSupportPoint_fst {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivWithinAt g (gD t) (Ioi t) t)
    (hgD : HasDerivWithinAt gD gDD (Ioi t) t) :
    HasDerivWithinAt (fun s => (Reference.companionSupportPoint g gD s).1)
      (-(g t + gDD) * Real.cos t) (Ioi t) t := by
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, neg_mul] using
    (hasDerivWithinAt_supportPoint_snd hg hgD).fun_neg

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
  simp only [coordDet, Reference.supportPoint, supportPointDX, supportPointDY]
  linear_combination f t * (f t + fDD t) * Real.sin_sq_add_cos_sq t

theorem coordDet_companionSupportPoint (g gD gDD : ℝ → ℝ) (t : ℝ) :
    coordDet (Reference.companionSupportPoint g gD t)
      (companionSupportPointDX g gDD t, companionSupportPointDY g gDD t) =
      g t * (g t + gDD t) := by
  simp only [companionSupportPoint_coordinates, coordDet, companionSupportPointDX,
    companionSupportPointDY]
  linear_combination g t * (g t + gDD t) * Real.sin_sq_add_cos_sq t

/-- The graph formula combined with integration by parts for the support density
`f (f + f'')`. This is the common analytic calculation for either upper support
quarter; all endpoint products are explicit, including the products which encode
the two vertical side faces. -/
theorem support_energy_graph_identity
    {a b : ℝ} {F X Y XD YD f fD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hXD : ∀ t ∈ Ioo a b, HasDerivWithinAt X (XD t) (Ioi t) t)
    (hYD : ∀ t ∈ Ioo a b, HasDerivWithinAt Y (YD t) (Ioi t) t)
    (hXDi : IntervalIntegrable XD volume a b) (hYDi : IntervalIntegrable YD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t)
    (hf : Continuous f) (hfD : Continuous fD)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hsecond : ∀ t ∈ Ioo a b, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume a b)
    (hdet : ∀ t ∈ Ioo a b, coordDet (X t, Y t) (XD t, YD t) = f t * (f t + fDD t)) :
    2 * (∫ x in X a..X b, F x) =
      (X b * Y b - f b * fD b) - (X a * Y a - f a * fD a) -
        ∫ t in a..b, f t ^ 2 - fD t ^ 2 := by
  have hI := ((hfD.fun_mul hfD).intervalIntegrable a b).add (hfDD.continuousOn_mul hf.continuousOn)
  have hdensity : ∫ t in a..b, coordDet (X t, Y t) (XD t, YD t) =
      ∫ t in a..b, (f t ^ 2 - fD t ^ 2) + (fD t * fD t + f t * fDD t) :=
    intervalIntegral.integral_congr_Ioo_of_le hab fun t ht => by rw [hdet t ht]; ring
  rw [intervalIntegral.integral_add (((hf.fun_pow 2).fun_sub (hfD.fun_pow 2)).intervalIntegrable
    a b) hI, intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hf.fun_mul hfD).continuousOn (fun t ht => (hderiv t ht).mul (hsecond t ht)) hI] at hdensity
  linarith [twice_integral_graph_parametrization hab hX hY hXD hYD hXDi hYDi hF hgraph]

/-- A point attaining an upward support is the actual roof point over its
own abscissa. The sine condition makes the normal genuinely upward-facing. -/
theorem IsDownwardCap.capRoof_eq_of_support_eq {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) {θ : ℝ} (hsin : 0 < Real.sin θ)
    (hsupport : coordDot p (unitNormal θ) = support U (unitNormal θ)) :
    capRoof U p.1 = p.2 := by
  refine le_antisymm ?_ (le_capRoof hU.isCompact hp)
  have h := hsupport ▸ coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (mem_image_of_mem Prod.fst hp)) (unitNormal θ)
  simp only [coordDot, unitNormal] at h
  exact le_of_mul_le_mul_right (by linarith) hsin

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
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hFc : Continuous (Reference.supportPoint f fD) := by unfold Reference.supportPoint; fun_prop
  have hGc : Continuous (Reference.companionSupportPoint g gD) := by
    unfold Reference.companionSupportPoint Reference.supportPoint rotate; fun_prop
  have hFrho := (hf.intervalIntegrable 0 (Real.pi / 2)).add hfDD
  have hGrho := (hg.intervalIntegrable 0 (Real.pi / 2)).add hgDD
  have hFenergy := support_energy_graph_identity hL hFc.fst.continuousOn hFc.snd.continuousOn
    (fun t ht => hasDerivWithinAt_supportPoint_fst (hderivF t ht) (hsecondF t ht))
    (fun t ht => hasDerivWithinAt_supportPoint_snd (hderivF t ht) (hsecondF t ht))
    (hFrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hFrho.mul_continuousOn Real.continuous_cos.continuousOn)
    (hU.continuousOn_capRoof.mono (image_subset_iff.2 fun t ht =>
      mem_image_of_mem Prod.fst (hFpoints t ht)))
    (fun t ht => hU.capRoof_eq_of_support_eq (hFpoints t (Ioo_subset_Icc_self ht))
      (sin_cos_pos_of_mem_quarter ht).1
      (by rw [Reference.coordDot_supportPoint, Reference.supportProjection_self, hFsupport t ht]))
    hf hfD hderivF hsecondF hfDD (fun t _ => coordDet_supportPoint f fD fDD t)
  have hGenergy := support_energy_graph_identity hL hGc.fst.continuousOn hGc.snd.continuousOn
    (fun t ht => hasDerivWithinAt_companionSupportPoint_fst (hderivG t ht) (hsecondG t ht))
    (fun t ht => hasDerivWithinAt_companionSupportPoint_snd (hderivG t ht) (hsecondG t ht))
    (hGrho.neg.mul_continuousOn Real.continuous_cos.continuousOn)
    (hGrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hU.continuousOn_capRoof.mono (image_subset_iff.2 fun t ht =>
      mem_image_of_mem Prod.fst (hGpoints t ht)))
    (fun t ht => hU.capRoof_eq_of_support_eq (θ := t + Real.pi / 2)
      (hGpoints t (Ioo_subset_Icc_self ht))
      (Real.sin_add_pi_div_two t ▸
        (sin_cos_pos_of_mem_quarter ht).2)
      (by rw [Reference.coordDot_companionSupportPoint, add_sub_cancel_right,
        Reference.supportProjection_self, hGsupport t ht]))
    hg hgD hderivG hsecondG hgDD (fun t _ => coordDet_companionSupportPoint g gD gDD t)
  simp only [Reference.supportPoint, companionSupportPoint_coordinates, Real.cos_zero,
    Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, hFtop, hGtop, mul_one, mul_zero,
    sub_zero, zero_sub] at hFenergy hGenergy
  rw [intervalIntegral.integral_add
    (((hf.fun_pow 2).fun_sub (hfD.fun_pow 2)).intervalIntegrable _ _)
    (((hg.fun_pow 2).fun_sub (hgD.fun_pow 2)).intervalIntegrable _ _)]
  linarith [hU.volumeReal_eq_wing_integrals hleft hright hfaceOrder hface]

end AmbidextrousSofa
