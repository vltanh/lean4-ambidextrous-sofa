module

public import AmbidextrousSofa.Measure.SupportArea
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.TietzeExtension

@[expose] public section

/-!
# Absolutely continuous graph and support area

The parameter curves and their first support derivatives are absolutely
continuous. All derivative assertions are almost everywhere assertions.
The oriented graph identity retains its endpoint products and permits a
collapsed or reversed arc. A continuous extension of the actual graph
function is used only to apply the ordinary primitive chain rule.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem integral_eq_sub_of_ac_of_ae_hasDerivAt
    {a b : ℝ} {E D : ℝ → ℝ} (hab : a ≤ b)
    (hE : AbsolutelyContinuousOnInterval E a b)
    (hD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt E (D t) t) :
    (∫ t in a..b, D t) = E b - E a := by
  refine (intervalIntegral.integral_congr_ae_restrict ?_).trans hE.integral_deriv_eq_sub
  rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  exact hD.mono fun _ h => h.deriv.symm

/-- Substitution along an absolutely continuous graph. There is no
injectivity or monotonicity premise on its abscissa. -/
theorem integral_graph_parametrization_ac {a b : ℝ} {F X Y XD : ℝ → ℝ}
    (hab : a ≤ b) (hX : AbsolutelyContinuousOnInterval X a b)
    (hXD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt X (XD t) t)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t) :
    (∫ x in X a..X b, F x) = ∫ t in a..b, Y t * XD t := by
  have hS : IsCompact (X '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (uIcc_of_le hab ▸ hX.continuousOn)
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hS.isClosed ⟨_, hF.domRestrict⟩
  have hGF : EqOn G F (X '' Icc a b) := fun x hx => congrArg (· ⟨x, hx⟩) hG
  have hP (x : ℝ) : HasDerivAt (fun x => ∫ s in X a..x, G s) (G x) x :=
    (G.continuous.integral_hasStrictDerivAt (X a) x).hasDerivAt
  have hC : ContDiff ℝ 1 fun x => ∫ s in X a..x, G s := contDiff_one_iff_deriv.2
    ⟨fun x => (hP x).differentiableAt, by rw [funext fun x => (hP x).deriv]; exact G.continuous⟩
  obtain ⟨L, hL⟩ := hC.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt hab
    (hL.comp_absolutelyContinuousOnInterval (uIcc_of_le hab ▸ mapsTo_image X _) hX)
    (hXD.mono fun t ht => (hP (X t)).comp t ht)
  simp only [Function.comp_apply, intervalIntegral.integral_same, sub_zero] at h
  calc (∫ x in X a..X b, F x) = ∫ x in X a..X b, G x := intervalIntegral.integral_congr
        fun x hx => (hGF (uIcc_of_le hab ▸ intermediate_value_uIcc hX.continuousOn hx)).symm
    _ = ∫ t in a..b, Y t * XD t := h.symm.trans <| intervalIntegral.integral_congr_Ioo_of_le hab
        fun t ht => by simp only [hGF (mem_image_of_mem X (Ioo_subset_Icc_self ht)), hgraph t ht]

theorem twice_integral_graph_parametrization_ac
    {a b : ℝ} {F X Y XD YD : ℝ → ℝ}
    (hab : a ≤ b) (hX : AbsolutelyContinuousOnInterval X a b)
    (hY : AbsolutelyContinuousOnInterval Y a b)
    (hXD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt X (XD t) t)
    (hYD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt Y (YD t) t)
    (hXDi : IntervalIntegrable XD volume a b) (hYDi : IntervalIntegrable YD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t) :
    2 * (∫ x in X a..X b, F x) = X b * Y b - X a * Y a -
      ∫ t in a..b, coordDet (X t, Y t) (XD t, YD t) := by
  have hXY := hYDi.continuousOn_mul hX.continuousOn
  have hYX := hXDi.continuousOn_mul hY.continuousOn
  have hparts := integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hX.fun_mul hY)
    ((hXD.and hYD).mono fun t h => h.1.mul h.2)
  rw [intervalIntegral.integral_add (hXDi.mul_continuousOn hY.continuousOn) hXY] at hparts
  simp only [coordDet, intervalIntegral.integral_sub hXY hYX, mul_comm (XD _),
    integral_graph_parametrization_ac hab hX hXD hF hgraph] at hparts ⊢
  linarith

theorem hasDerivAt_supportPoint_fst {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivAt f (fD t) t) (hfD : HasDerivAt fD fDD t) :
    HasDerivAt (fun s => (Reference.supportPoint f fD s).1)
      (-(f t + fDD) * Real.sin t) t :=
  ((hf.mul (Real.hasDerivAt_cos t)).sub (hfD.mul (Real.hasDerivAt_sin t))).congr_deriv (by ring)

theorem hasDerivAt_supportPoint_snd {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivAt f (fD t) t) (hfD : HasDerivAt fD fDD t) :
    HasDerivAt (fun s => (Reference.supportPoint f fD s).2)
      ((f t + fDD) * Real.cos t) t :=
  ((hf.mul (Real.hasDerivAt_sin t)).add (hfD.mul (Real.hasDerivAt_cos t))).congr_deriv (by ring)

theorem hasDerivAt_companionSupportPoint_fst {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivAt g (gD t) t) (hgD : HasDerivAt gD gDD t) :
    HasDerivAt (fun s => (Reference.companionSupportPoint g gD s).1)
      (-(g t + gDD) * Real.cos t) t := by
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, neg_mul] using
    (hasDerivAt_supportPoint_snd hg hgD).fun_neg

theorem hasDerivAt_companionSupportPoint_snd {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivAt g (gD t) t) (hgD : HasDerivAt gD gDD t) :
    HasDerivAt (fun s => (Reference.companionSupportPoint g gD s).2)
      (-(g t + gDD) * Real.sin t) t := by
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, add_zero] using
    hasDerivAt_supportPoint_fst hg hgD

theorem absolutelyContinuousOnInterval_supportPoint
    {a b : ℝ} {f fD : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfD : AbsolutelyContinuousOnInterval fD a b) :
    AbsolutelyContinuousOnInterval (fun t => (Reference.supportPoint f fD t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (Reference.supportPoint f fD t).2) a b := by
  have hc := Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hs := Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  exact ⟨(hf.fun_mul hc).sub (hfD.fun_mul hs), (hf.fun_mul hs).add (hfD.fun_mul hc)⟩

theorem absolutelyContinuousOnInterval_companionSupportPoint
    {a b : ℝ} {g gD : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hgD : AbsolutelyContinuousOnInterval gD a b) :
    AbsolutelyContinuousOnInterval (fun t => (Reference.companionSupportPoint g gD t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (Reference.companionSupportPoint g gD t).2) a b := by
  obtain ⟨h1, h2⟩ := absolutelyContinuousOnInterval_supportPoint hg hgD
  exact ⟨h2.neg.congr fun t _ => by simp [Reference.companionSupportPoint, rotate],
    h1.congr fun t _ => by simp [Reference.companionSupportPoint, rotate]⟩

/-- The absolutely continuous graph formula combined with integration by parts for
the support density `f (f + f'')`; all endpoint products are explicit. -/
theorem support_energy_graph_identity_ac
    {a b : ℝ} {F X Y XD YD f fD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hX : AbsolutelyContinuousOnInterval X a b)
    (hY : AbsolutelyContinuousOnInterval Y a b)
    (hXD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt X (XD t) t)
    (hYD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt Y (YD t) t)
    (hXDi : IntervalIntegrable XD volume a b) (hYDi : IntervalIntegrable YD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t)
    (hf : AbsolutelyContinuousOnInterval f a b) (hfD : AbsolutelyContinuousOnInterval fD a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t)
    (hsecond : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt fD (fDD t) t)
    (hfDD : IntervalIntegrable fDD volume a b)
    (hdet : ∀ t ∈ Ioo a b, coordDet (X t, Y t) (XD t, YD t) = f t * (f t + fDD t)) :
    2 * (∫ x in X a..X b, F x) =
      (X b * Y b - f b * fD b) - (X a * Y a - f a * fD a) -
        ∫ t in a..b, f t ^ 2 - fD t ^ 2 := by
  have hdensity : ∫ t in a..b, coordDet (X t, Y t) (XD t, YD t) =
      ∫ t in a..b, (f t ^ 2 - fD t ^ 2) + (fD t * fD t + f t * fDD t) :=
    intervalIntegral.integral_congr_Ioo_of_le hab fun t ht => by rw [hdet t ht]; ring
  rw [intervalIntegral.integral_add
    ((hf.continuousOn.fun_pow 2).fun_sub (hfD.continuousOn.fun_pow 2)).intervalIntegrable
    ((hfD.continuousOn.fun_mul hfD.continuousOn).intervalIntegrable.add
      (hfDD.continuousOn_mul hf.continuousOn)),
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hf.fun_mul hfD)
      ((hderiv.and hsecond).mono fun t h => h.1.mul h.2)] at hdensity
  linarith [twice_integral_graph_parametrization_ac hab hX hY hXD hYD hXDi hYDi hF hgraph]

/-- The actual area formula with only absolutely continuous support
derivatives. The top face and both vertical axis faces remain in the
endpoint terms until the two roof integrals are joined. -/
theorem IsDownwardCap.volumeReal_eq_support_energy_ac
    {U : Set Plane} (hU : IsDownwardCap U) {f g fD gD fDD gDD : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 (Real.pi / 2))
    (hg : AbsolutelyContinuousOnInterval g 0 (Real.pi / 2))
    (hfD : AbsolutelyContinuousOnInterval fD 0 (Real.pi / 2))
    (hgD : AbsolutelyContinuousOnInterval gD 0 (Real.pi / 2))
    (hderivF : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt f (fD t) t)
    (hderivG : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt g (gD t) t)
    (hsecondF : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt fD (fDD t) t)
    (hsecondG : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt gD (gDD t) t)
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
  have hFc := absolutelyContinuousOnInterval_supportPoint hf hfD
  have hGc := absolutelyContinuousOnInterval_companionSupportPoint hg hgD
  have hFrho := hf.continuousOn.intervalIntegrable.add hfDD
  have hGrho := hg.continuousOn.intervalIntegrable.add hgDD
  have hFenergy := support_energy_graph_identity_ac hL hFc.1 hFc.2
    ((hderivF.and hsecondF).mono fun t h => hasDerivAt_supportPoint_fst h.1 h.2)
    ((hderivF.and hsecondF).mono fun t h => hasDerivAt_supportPoint_snd h.1 h.2)
    (hFrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hFrho.mul_continuousOn Real.continuous_cos.continuousOn)
    (hU.continuousOn_capRoof.mono (image_subset_iff.2 fun t ht =>
      mem_image_of_mem Prod.fst (hFpoints t ht)))
    (fun t ht => hU.capRoof_eq_of_support_eq (hFpoints t (Ioo_subset_Icc_self ht))
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]))
      (by rw [Reference.coordDot_supportPoint, Reference.supportProjection_self, hFsupport t ht]))
    hf hfD hderivF hsecondF hfDD (fun t _ => coordDet_supportPoint f fD fDD t)
  have hGenergy := support_energy_graph_identity_ac hL hGc.1 hGc.2
    ((hderivG.and hsecondG).mono fun t h => hasDerivAt_companionSupportPoint_fst h.1 h.2)
    ((hderivG.and hsecondG).mono fun t h => hasDerivAt_companionSupportPoint_snd h.1 h.2)
    (hGrho.neg.mul_continuousOn Real.continuous_cos.continuousOn)
    (hGrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hU.continuousOn_capRoof.mono (image_subset_iff.2 fun t ht =>
      mem_image_of_mem Prod.fst (hGpoints t ht)))
    (fun t ht => hU.capRoof_eq_of_support_eq (θ := t + Real.pi / 2)
      (hGpoints t (Ioo_subset_Icc_self ht))
      (Real.sin_add_pi_div_two t ▸
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      (by rw [Reference.coordDot_companionSupportPoint, add_sub_cancel_right,
        Reference.supportProjection_self, hGsupport t ht]))
    hg hgD hderivG hsecondG hgDD (fun t _ => coordDet_companionSupportPoint g gD gDD t)
  simp only [Reference.supportPoint, companionSupportPoint_coordinates, Real.cos_zero,
    Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, hFtop, hGtop, mul_one, mul_zero,
    sub_zero, zero_sub] at hFenergy hGenergy
  rw [intervalIntegral.integral_add
    ((hf.continuousOn.fun_pow 2).fun_sub (hfD.continuousOn.fun_pow 2)).intervalIntegrable
    ((hg.continuousOn.fun_pow 2).fun_sub (hgD.continuousOn.fun_pow 2)).intervalIntegrable]
  linarith [hU.volumeReal_eq_wing_integrals hleft hright hfaceOrder hface]

end AmbidextrousSofa
