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
  rw [← hE.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  exact hD.mono (fun _ h => h.deriv.symm)

/-- Substitution along an absolutely continuous graph. There is no
injectivity or monotonicity premise on its abscissa. -/
theorem integral_graph_parametrization_ac {a b : ℝ} {F X Y XD : ℝ → ℝ}
    (hab : a ≤ b) (hX : AbsolutelyContinuousOnInterval X a b)
    (hXD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt X (XD t) t)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t) :
    (∫ x in X a..X b, F x) = ∫ t in a..b, Y t * XD t := by
  have hXc : ContinuousOn X (Icc a b) := by
    simpa only [uIcc_of_le hab] using hX.continuousOn
  let S := X '' Icc a b
  have hS : IsCompact S := isCompact_Icc.image_of_continuousOn hXc
  let Fc : C(S, ℝ) := ⟨fun x => F x, continuousOn_iff_continuous_restrict.mp hF⟩
  obtain ⟨G, hG⟩ := Fc.exists_restrict_eq hS.isClosed
  have hGeq : EqOn G F S := by
    intro x hx
    exact congrArg (fun H : C(S, ℝ) => H ⟨x, hx⟩) hG
  let P : ℝ → ℝ := fun x => ∫ s in X a..x, G s
  have hP (x : ℝ) : HasDerivAt P (G x) x :=
    (G.continuous.integral_hasStrictDerivAt (X a) x).hasDerivAt
  obtain ⟨K, hK⟩ := hX.exists_bound
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (G.continuous.continuousOn (s := Icc (-K) K))
  have hPlip : LipschitzOnWith ⟨max M 0, le_max_right _ _⟩ P (Icc (-K) K) := by
    apply (convex_Icc (-K) K).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hP x).hasDerivWithinAt)
    intro x hx
    change ‖G x‖ ≤ max M 0
    exact (hM x hx).trans (le_max_left _ _)
  have hmap : MapsTo X (uIcc a b) (Icc (-K) K) := by
    intro t ht
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hK t ht)
  have hPX : AbsolutelyContinuousOnInterval (P ∘ X) a b :=
    hPlip.comp_absolutelyContinuousOnInterval hmap hX
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (P ∘ X) (G (X t) * XD t) t :=
    hXD.mono (fun t ht => (hP (X t)).comp t ht)
  have hprimitive := integral_eq_sub_of_ac_of_ae_hasDerivAt hab hPX hderiv
  simp only [Function.comp_apply, P, intervalIntegral.integral_same, sub_zero] at hprimitive
  calc
    (∫ x in X a..X b, F x) = ∫ x in X a..X b, G x := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply (hGeq (x := x) ?_).symm
      have hmem := intermediate_value_uIcc hX.continuousOn hx
      simpa only [uIcc_of_le hab] using hmem
    _ = ∫ t in a..b, G (X t) * XD t := hprimitive.symm
    _ = ∫ t in a..b, Y t * XD t := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro t ht
      dsimp only
      rw [hGeq (mem_image_of_mem X ⟨ht.1.le, ht.2.le⟩), hgraph t ht]

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
  have hparts : (∫ t in a..b, XD t * Y t + X t * YD t) =
      X b * Y b - X a * Y a := by
    apply integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hX.fun_mul hY)
    filter_upwards [hXD, hYD] with t hx hy
    exact hx.mul hy
  rw [intervalIntegral.integral_add
    (hXDi.mul_continuousOn hY.continuousOn) hXY] at hparts
  have hcomm : (∫ t in a..b, XD t * Y t) = ∫ t in a..b, Y t * XD t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hcomm] at hparts
  rw [integral_graph_parametrization_ac hab hX hXD hF hgraph]
  simp only [coordDet]
  rw [intervalIntegral.integral_sub hXY hYX]
  linarith

theorem hasDerivAt_supportPoint_fst {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivAt f (fD t) t) (hfD : HasDerivAt fD fDD t) :
    HasDerivAt (fun s => (Reference.supportPoint f fD s).1)
      (-(f t + fDD) * Real.sin t) t := by
  unfold Reference.supportPoint
  apply ((hf.mul (Real.hasDerivAt_cos t)).sub
    (hfD.mul (Real.hasDerivAt_sin t))).congr_deriv
  ring

theorem hasDerivAt_supportPoint_snd {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivAt f (fD t) t) (hfD : HasDerivAt fD fDD t) :
    HasDerivAt (fun s => (Reference.supportPoint f fD s).2)
      ((f t + fDD) * Real.cos t) t := by
  unfold Reference.supportPoint
  apply ((hf.mul (Real.hasDerivAt_sin t)).add
    (hfD.mul (Real.hasDerivAt_cos t))).congr_deriv
  ring

theorem hasDerivAt_companionSupportPoint_fst {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivAt g (gD t) t) (hgD : HasDerivAt gD gDD t) :
    HasDerivAt (fun s => (Reference.companionSupportPoint g gD s).1)
      (-(g t + gDD) * Real.cos t) t := by
  have h := (hasDerivAt_supportPoint_snd hg hgD).fun_neg
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, neg_mul] using h

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
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval
  exact ⟨(hf.fun_mul hc).sub (hfD.fun_mul hs), (hf.fun_mul hs).add (hfD.fun_mul hc)⟩

theorem absolutelyContinuousOnInterval_companionSupportPoint
    {a b : ℝ} {g gD : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hgD : AbsolutelyContinuousOnInterval gD a b) :
    AbsolutelyContinuousOnInterval (fun t => (Reference.companionSupportPoint g gD t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (Reference.companionSupportPoint g gD t).2) a b := by
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval
  constructor
  · apply ((hg.neg.fun_mul hs).sub (hgD.fun_mul hc)).congr
    intro t _
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [companionSupportPoint_coordinates]
  · apply ((hg.fun_mul hc).sub (hgD.fun_mul hs)).congr
    intro t _
    simp only [Pi.sub_apply]
    rw [companionSupportPoint_coordinates]

theorem integral_support_density_ac {a b : ℝ} {f fD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hfD : AbsolutelyContinuousOnInterval fD a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t)
    (hsecond : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt fD (fDD t) t)
    (hfDD : IntervalIntegrable fDD volume a b) :
    (∫ t in a..b, f t * (f t + fDD t)) =
      (∫ t in a..b, f t ^ 2 - fD t ^ 2) + f b * fD b - f a * fD a := by
  have hfDi : IntervalIntegrable fD volume a b := hfD.continuousOn.intervalIntegrable
  have henergy : IntervalIntegrable (fun t => f t ^ 2 - fD t ^ 2) volume a b :=
    ((hf.continuousOn.pow 2).sub (hfD.continuousOn.pow 2)).intervalIntegrable
  have hpartsI : IntervalIntegrable (fun t => fD t * fD t + f t * fDD t) volume a b :=
    (hfDi.mul_continuousOn hfD.continuousOn).add (hfDD.continuousOn_mul hf.continuousOn)
  have hparts : (∫ t in a..b, fD t * fD t + f t * fDD t) =
      f b * fD b - f a * fD a := by
    apply integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hf.fun_mul hfD)
    filter_upwards [hderiv, hsecond] with t ht hDt
    exact ht.mul hDt
  calc
    _ = ∫ t in a..b, (f t ^ 2 - fD t ^ 2) +
        (fD t * fD t + f t * fDD t) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by rw [intervalIntegral.integral_add henergy hpartsI, hparts]; ring

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
  have hgraphInt := twice_integral_graph_parametrization_ac hab hX hY hXD hYD hXDi hYDi hF hgraph
  have hdetInt : (∫ t in a..b, coordDet (X t, Y t) (XD t, YD t)) =
      ∫ t in a..b, f t * (f t + fDD t) :=
    intervalIntegral.integral_congr_Ioo_of_le hab hdet
  rw [hdetInt, integral_support_density_ac hab hf hfD hderiv hsecond hfDD] at hgraphInt
  linarith

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
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hFc := absolutelyContinuousOnInterval_supportPoint hf hfD
  have hGc := absolutelyContinuousOnInterval_companionSupportPoint hg hgD
  have hFrho : IntervalIntegrable (fun t => f t + fDD t) volume 0 (Real.pi / 2) :=
    hf.continuousOn.intervalIntegrable.add hfDD
  have hGrho : IntervalIntegrable (fun t => g t + gDD t) volume 0 (Real.pi / 2) :=
    hg.continuousOn.intervalIntegrable.add hgDD
  have hFXDi : IntervalIntegrable (supportPointDX f fDD) volume 0 (Real.pi / 2) :=
    hFrho.neg.mul_continuousOn Real.continuous_sin.continuousOn
  have hFYDi : IntervalIntegrable (supportPointDY f fDD) volume 0 (Real.pi / 2) :=
    hFrho.mul_continuousOn Real.continuous_cos.continuousOn
  have hGXDi : IntervalIntegrable (companionSupportPointDX g gDD) volume 0 (Real.pi / 2) :=
    hGrho.neg.mul_continuousOn Real.continuous_cos.continuousOn
  have hGYDi : IntervalIntegrable (companionSupportPointDY g gDD) volume 0 (Real.pi / 2) :=
    hGrho.neg.mul_continuousOn Real.continuous_sin.continuousOn
  have hFXD : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt (fun s => (Reference.supportPoint f fD s).1) (supportPointDX f fDD t) t := by
    filter_upwards [hderivF, hsecondF] with t ht htD
    exact hasDerivAt_supportPoint_fst ht htD
  have hFYD : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt (fun s => (Reference.supportPoint f fD s).2) (supportPointDY f fDD t) t := by
    filter_upwards [hderivF, hsecondF] with t ht htD
    exact hasDerivAt_supportPoint_snd ht htD
  have hGXD : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt (fun s => (Reference.companionSupportPoint g gD s).1)
        (companionSupportPointDX g gDD t) t := by
    filter_upwards [hderivG, hsecondG] with t ht htD
    exact hasDerivAt_companionSupportPoint_fst ht htD
  have hGYD : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt (fun s => (Reference.companionSupportPoint g gD s).2)
        (companionSupportPointDY g gDD t) t := by
    filter_upwards [hderivG, hsecondG] with t ht htD
    exact hasDerivAt_companionSupportPoint_snd ht htD
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
  have hFenergy := support_energy_graph_identity_ac hL hFc.1 hFc.2 hFXD hFYD
    hFXDi hFYDi hFroof hFgraph hf hfD hderivF hsecondF hfDD
    (fun t _ => coordDet_supportPoint f fD fDD t)
  have hGenergy := support_energy_graph_identity_ac hL hGc.1 hGc.2 hGXD hGYD
    hGXDi hGYDi hGroof hGgraph hg hgD hderivG hsecondG hgDD
    (fun t _ => coordDet_companionSupportPoint g gD gDD t)
  simp only [Reference.supportPoint, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero,
    zero_sub, hFtop, one_mul] at hFenergy
  simp only [companionSupportPoint_coordinates, Real.cos_zero, Real.sin_zero,
    Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_mul, zero_add,
    add_zero, sub_zero, zero_sub, hGtop, one_mul, neg_mul] at hGenergy
  have harea := hU.volumeReal_eq_wing_integrals hleft hright hfaceOrder hface
  have hFi : IntervalIntegrable (fun t => f t ^ 2 - fD t ^ 2) volume 0 (Real.pi / 2) :=
    ((hf.continuousOn.pow 2).sub (hfD.continuousOn.pow 2)).intervalIntegrable
  have hGi : IntervalIntegrable (fun t => g t ^ 2 - gD t ^ 2) volume 0 (Real.pi / 2) :=
    ((hg.continuousOn.pow 2).sub (hgD.continuousOn.pow 2)).intervalIntegrable
  rw [intervalIntegral.integral_add hFi hGi]
  nlinarith

end AmbidextrousSofa
