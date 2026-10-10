import AmbidextrousSofa.Measure.SignedRoofIntegral
import AmbidextrousSofa.Measure.SupportAreaAC

/-!
# Signed roof integration for absolutely continuous support derivatives

The three arcs are actual graphs of one continuous function. Their support
derivatives are absolutely continuous and their second derivatives are only
specified almost everywhere. The endpoint terms retain the actual one-sided
face traces until the two contact equations cancel them.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem integral_firstTangent_density_ac {a b : ℝ} {f g fD gD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hg : Continuous g)
    (hfD : Continuous fD) (hgD : Continuous gD)
    (hfAC : AbsolutelyContinuousOnInterval f a b)
    (hgAC : AbsolutelyContinuousOnInterval g a b)
    (hfDAC : AbsolutelyContinuousOnInterval fD a b)
    (hderivF : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t)
    (hderivG : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt g (gD t) t)
    (hsecondF : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt fD (fDD t) t)
    (hfDD : IntervalIntegrable fDD volume a b) :
    (∫ t in a..b, (f t - 1) * (f t - 1 + fDD t)) =
      (∫ t in a..b, cornerDensity f g fD gD t) -
      (∫ t in a..b, supportP fD g t ^ 2) +
      firstMomentumPrimitive f g fD b - firstMomentumPrimitive f g fD a := by
  have hp : Continuous (supportP fD g) := (hfD.sub hg).add continuous_const
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ
    fun_prop
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hprimitive : AbsolutelyContinuousOnInterval (firstMomentumPrimitive f g fD) a b :=
    (hfAC.sub hconst).mul ((hfDAC.sub hgAC).add hconst)
  have hd : IntervalIntegrable (firstMomentumDerivative f g fD gD fDD) volume a b :=
    ((hfD.mul hp).intervalIntegrable _ _).add
      ((hfDD.sub (hgD.intervalIntegrable _ _)).continuousOn_mul
        (hf.sub continuous_const).continuousOn)
  have hftc : (∫ t in a..b, firstMomentumDerivative f g fD gD fDD t) =
      firstMomentumPrimitive f g fD b - firstMomentumPrimitive f g fD a := by
    apply integral_eq_sub_of_ac_of_ae_hasDerivAt hab hprimitive
    filter_upwards [hderivF, hderivG, hsecondF] with t hdf hdg hddf
    exact (hdf.sub_const 1).mul ((hddf.sub hdg).add_const 1)
  calc
    _ = ∫ t in a..b, (cornerDensity f g fD gD t - supportP fD g t ^ 2) +
        firstMomentumDerivative f g fD gD fDD t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact firstTangent_density_identity f g fD gD fDD t
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((hc.intervalIntegrable _ _).sub ((hp.pow 2).intervalIntegrable _ _)) hd,
        intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
          ((hp.pow 2).intervalIntegrable _ _), hftc]
      ring

theorem integral_secondTangent_density_ac {a b : ℝ} {f g fD gD gDD : ℝ → ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hg : Continuous g)
    (hfD : Continuous fD) (hgD : Continuous gD)
    (hfAC : AbsolutelyContinuousOnInterval f a b)
    (hgAC : AbsolutelyContinuousOnInterval g a b)
    (hgDAC : AbsolutelyContinuousOnInterval gD a b)
    (hderivF : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t)
    (hderivG : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt g (gD t) t)
    (hsecondG : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt gD (gDD t) t)
    (hgDD : IntervalIntegrable gDD volume a b) :
    (∫ t in a..b, (g t - 1) * (g t - 1 + gDD t)) =
      (∫ t in a..b, cornerDensity f g fD gD t) -
      (∫ t in a..b, supportQ gD f t ^ 2) +
      secondMomentumPrimitive f g gD b - secondMomentumPrimitive f g gD a := by
  have hq : Continuous (supportQ gD f) := (hgD.add hf).sub continuous_const
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ
    fun_prop
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hprimitive : AbsolutelyContinuousOnInterval (secondMomentumPrimitive f g gD) a b :=
    (hgAC.sub hconst).mul ((hgDAC.add hfAC).sub hconst)
  have hd : IntervalIntegrable (secondMomentumDerivative f g fD gD gDD) volume a b :=
    ((hgD.mul hq).intervalIntegrable _ _).add
      ((hgDD.add (hfD.intervalIntegrable _ _)).continuousOn_mul
        (hg.sub continuous_const).continuousOn)
  have hftc : (∫ t in a..b, secondMomentumDerivative f g fD gD gDD t) =
      secondMomentumPrimitive f g gD b - secondMomentumPrimitive f g gD a := by
    apply integral_eq_sub_of_ac_of_ae_hasDerivAt hab hprimitive
    filter_upwards [hderivF, hderivG, hsecondG] with t hdf hdg hddg
    exact (hdg.sub_const 1).mul ((hddg.add hdf).sub_const 1)
  calc
    _ = ∫ t in a..b, (cornerDensity f g fD gD t - supportQ gD f t ^ 2) +
        secondMomentumDerivative f g fD gD gDD t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact secondTangent_density_identity f g fD gD gDD t
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((hc.intervalIntegrable _ _).sub ((hq.pow 2).intervalIntegrable _ _)) hd,
        intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
          ((hq.pow 2).intervalIntegrable _ _), hftc]
      ring

/-- The middle graph arc is traversed in reverse. Absolute continuity of
the six coordinates is enough; no multiplicity or injectivity premise is
needed for this identity of oriented graph integrals. -/
theorem twice_integral_three_graph_arcs_ac
    {a b d e : ℝ} {F : ℝ → ℝ} {P Q R : ℝ → Plane}
    {PX PY QX QY RX RY : ℝ → ℝ}
    (had : a ≤ d) (hbd : b ≤ d) (hbe : b ≤ e)
    (hPXac : AbsolutelyContinuousOnInterval (fun t => (P t).1) a d)
    (hPYac : AbsolutelyContinuousOnInterval (fun t => (P t).2) a d)
    (hQXac : AbsolutelyContinuousOnInterval (fun t => (Q t).1) b d)
    (hQYac : AbsolutelyContinuousOnInterval (fun t => (Q t).2) b d)
    (hRXac : AbsolutelyContinuousOnInterval (fun t => (R t).1) b e)
    (hRYac : AbsolutelyContinuousOnInterval (fun t => (R t).2) b e)
    (hPX : ∀ᵐ t ∂volume.restrict (Ioo a d), HasDerivAt (fun s => (P s).1) (PX t) t)
    (hPY : ∀ᵐ t ∂volume.restrict (Ioo a d), HasDerivAt (fun s => (P s).2) (PY t) t)
    (hQX : ∀ᵐ t ∂volume.restrict (Ioo b d), HasDerivAt (fun s => (Q s).1) (QX t) t)
    (hQY : ∀ᵐ t ∂volume.restrict (Ioo b d), HasDerivAt (fun s => (Q s).2) (QY t) t)
    (hRX : ∀ᵐ t ∂volume.restrict (Ioo b e), HasDerivAt (fun s => (R s).1) (RX t) t)
    (hRY : ∀ᵐ t ∂volume.restrict (Ioo b e), HasDerivAt (fun s => (R s).2) (RY t) t)
    (hPXi : IntervalIntegrable PX volume a d) (hPYi : IntervalIntegrable PY volume a d)
    (hQXi : IntervalIntegrable QX volume b d) (hQYi : IntervalIntegrable QY volume b d)
    (hRXi : IntervalIntegrable RX volume b e) (hRYi : IntervalIntegrable RY volume b e)
    (hF : Continuous F)
    (hgraphP : ∀ t ∈ Ioo a d, F (P t).1 = (P t).2)
    (hgraphQ : ∀ t ∈ Ioo b d, F (Q t).1 = (Q t).2)
    (hgraphR : ∀ t ∈ Ioo b e, F (R t).1 = (R t).2)
    (hPQ : P d = Q d) (hQR : Q b = R b)
    (hPzero : (P a).2 = 0) (hRzero : (R e).2 = 0) :
    2 * (∫ x in (P a).1..(R e).1, F x) =
      -(∫ t in a..d, coordDet (P t) (PX t, PY t)) +
        (∫ t in b..d, coordDet (Q t) (QX t, QY t)) -
        ∫ t in b..e, coordDet (R t) (RX t, RY t) := by
  have hpi := twice_integral_graph_parametrization_ac had
    hPXac hPYac hPX hPY hPXi hPYi hF.continuousOn hgraphP
  have hqi := twice_integral_graph_parametrization_ac hbd
    hQXac hQYac hQX hQY hQXi hQYi hF.continuousOn hgraphQ
  have hri := twice_integral_graph_parametrization_ac hbe
    hRXac hRYac hRX hRY hRXi hRYi hF.continuousOn hgraphR
  rw [hPQ, hPzero, mul_zero] at hpi
  rw [← hQR, hRzero, mul_zero] at hri
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (P a).1 (Q b).1)
    (hF.intervalIntegrable (Q b).1 (Q d).1)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (P a).1 (Q b).1)
    (hF.intervalIntegrable (Q b).1 (R e).1)
  linarith

/-- Signed integration for the actual three graph arcs with measurable
curvature. All derivative assertions are almost everywhere on the open
quarter; the closed endpoint values remain the genuine continuous traces. -/
theorem signedRoof_integral_of_graphs_ac
    {b d : ℝ} {N f g fD gD fDD gDD : ℝ → ℝ}
    (hb0 : 0 ≤ b) (hbd : b ≤ d) (hdL : d ≤ Real.pi / 2)
    (hN : Continuous N) (hf : Continuous f) (hg : Continuous g)
    (hfD : Continuous fD) (hgD : Continuous gD)
    (hfAC : AbsolutelyContinuousOnInterval f 0 (Real.pi / 2))
    (hgAC : AbsolutelyContinuousOnInterval g 0 (Real.pi / 2))
    (hfDAC : AbsolutelyContinuousOnInterval fD 0 (Real.pi / 2))
    (hgDAC : AbsolutelyContinuousOnInterval gD 0 (Real.pi / 2))
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt f (fD t) t ∧ HasDerivAt g (gD t) t ∧
      HasDerivAt fD (fDD t) t ∧ HasDerivAt gD (gDD t) t)
    (hfDD : IntervalIntegrable fDD volume 0 (Real.pi / 2))
    (hgDD : IntervalIntegrable gDD volume 0 (Real.pi / 2))
    (hFtop : f (Real.pi / 2) = 1) (hGtop : g 0 = 1)
    (hpzero : supportP fD g b = 0) (hqzero : supportQ gD f d = 0)
    (hgraphD : ∀ t ∈ Ioo 0 d,
      N (secondTangentPoint g gD t).1 = (secondTangentPoint g gD t).2)
    (hgraphC : ∀ t ∈ Ioo b d,
      N (innerCornerPoint f g t).1 = (innerCornerPoint f g t).2)
    (hgraphB : ∀ t ∈ Ioo b (Real.pi / 2),
      N (firstTangentPoint f fD t).1 = (firstTangentPoint f fD t).2) :
    2 * (∫ x in (-gD 0)..(-fD (Real.pi / 2)), N x) =
      -(∫ t in (0 : ℝ)..(Real.pi / 2), cornerDensity f g fD gD t) +
      (∫ t in b..(Real.pi / 2), supportP fD g t ^ 2) +
      ∫ t in (0 : ℝ)..d, supportQ gD f t ^ 2 := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h0d : 0 ≤ d := hb0.trans hbd
  have hbL : b ≤ Real.pi / 2 := hbd.trans hdL
  have hsubD : uIcc (0 : ℝ) d ⊆ uIcc 0 (Real.pi / 2) := by
    rw [uIcc_of_le h0d, uIcc_of_le hL]
    exact Icc_subset_Icc le_rfl hdL
  have hsubC : uIcc b d ⊆ uIcc 0 (Real.pi / 2) := by
    rw [uIcc_of_le hbd, uIcc_of_le hL]
    exact Icc_subset_Icc hb0 hdL
  have hsubB : uIcc b (Real.pi / 2) ⊆ uIcc 0 (Real.pi / 2) := by
    rw [uIcc_of_le hbL, uIcc_of_le hL]
    exact Icc_subset_Icc hb0 le_rfl
  have hderivD := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) d ⊆ Ioo 0 (Real.pi / 2) from
      fun _ ht => ⟨ht.1, ht.2.trans_le hdL⟩) hderiv
  have hderivC := ae_restrict_of_ae_restrict_of_subset
    (show Ioo b d ⊆ Ioo 0 (Real.pi / 2) from
      fun _ ht => ⟨hb0.trans_lt ht.1, ht.2.trans_le hdL⟩) hderiv
  have hderivB := ae_restrict_of_ae_restrict_of_subset
    (show Ioo b (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2) from
      fun _ ht => ⟨hb0.trans_lt ht.1, ht.2⟩) hderiv
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 (Real.pi / 2) :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hsin : AbsolutelyContinuousOnInterval Real.sin 0 (Real.pi / 2) :=
    (show ContDiff ℝ 1 Real.sin by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hcos : AbsolutelyContinuousOnInterval Real.cos 0 (Real.pi / 2) :=
    (show ContDiff ℝ 1 Real.cos by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hBXac : AbsolutelyContinuousOnInterval (fun t => (firstTangentPoint f fD t).1)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hcos).sub (hfDAC.mul hsin)
  have hBYac : AbsolutelyContinuousOnInterval (fun t => (firstTangentPoint f fD t).2)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hsin).add (hfDAC.mul hcos)
  have hDXac : AbsolutelyContinuousOnInterval (fun t => (secondTangentPoint g gD t).1)
      0 (Real.pi / 2) := by
    simpa only [secondTangentPoint, companionSupportPoint_coordinates] using
      (((hgAC.sub hconst).neg.mul hsin).sub (hgDAC.mul hcos))
  have hDYac : AbsolutelyContinuousOnInterval (fun t => (secondTangentPoint g gD t).2)
      0 (Real.pi / 2) := by
    simpa only [secondTangentPoint, companionSupportPoint_coordinates] using
      (((hgAC.sub hconst).mul hcos).sub (hgDAC.mul hsin))
  have hCXac : AbsolutelyContinuousOnInterval (fun t => (innerCornerPoint f g t).1)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hcos).sub ((hgAC.sub hconst).mul hsin)
  have hCYac : AbsolutelyContinuousOnInterval (fun t => (innerCornerPoint f g t).2)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hsin).add ((hgAC.sub hconst).mul hcos)
  have hCXc : Continuous (innerCornerDX f g fD gD) := by
    unfold innerCornerDX supportP supportQ
    fun_prop
  have hCYc : Continuous (innerCornerDY f g fD gD) := by
    unfold innerCornerDY supportP supportQ
    fun_prop
  have hfDD' := hfDD.mono_set hsubB
  have hgDD' := hgDD.mono_set hsubD
  have hBrho : IntervalIntegrable (fun t => f t - 1 + fDD t) volume b (Real.pi / 2) :=
    ((hf.sub continuous_const).intervalIntegrable _ _).add hfDD'
  have hDrho : IntervalIntegrable (fun t => g t - 1 + gDD t) volume 0 d :=
    ((hg.sub continuous_const).intervalIntegrable _ _).add hgDD'
  have hBXi : IntervalIntegrable (supportPointDX (fun t => f t - 1) fDD)
      volume b (Real.pi / 2) :=
    hBrho.neg.mul_continuousOn Real.continuous_sin.continuousOn
  have hBYi : IntervalIntegrable (supportPointDY (fun t => f t - 1) fDD)
      volume b (Real.pi / 2) :=
    hBrho.mul_continuousOn Real.continuous_cos.continuousOn
  have hDXi : IntervalIntegrable (companionSupportPointDX (fun t => g t - 1) gDD) volume 0 d :=
    hDrho.neg.mul_continuousOn Real.continuous_cos.continuousOn
  have hDYi : IntervalIntegrable (companionSupportPointDY (fun t => g t - 1) gDD) volume 0 d :=
    hDrho.neg.mul_continuousOn Real.continuous_sin.continuousOn
  have hBzero : (firstTangentPoint f fD (Real.pi / 2)).2 = 0 := by
    simp only [firstTangentPoint, Reference.supportPoint, hFtop, sub_self,
      Real.sin_pi_div_two, Real.cos_pi_div_two, zero_mul, mul_zero, add_zero]
  have hDzero : (secondTangentPoint g gD 0).2 = 0 := by
    simp only [secondTangentPoint, companionSupportPoint_coordinates, hGtop,
      sub_self, Real.sin_zero, Real.cos_zero, zero_mul, mul_zero, sub_zero]
  have hgraphs := twice_integral_three_graph_arcs_ac h0d hbd hbL
    (hDXac.mono hsubD) (hDYac.mono hsubD) (hCXac.mono hsubC) (hCYac.mono hsubC)
    (hBXac.mono hsubB) (hBYac.mono hsubB)
    (by
      filter_upwards [hderivD] with t ht
      exact hasDerivAt_companionSupportPoint_fst (ht.2.1.sub_const 1) ht.2.2.2)
    (by
      filter_upwards [hderivD] with t ht
      exact hasDerivAt_companionSupportPoint_snd (ht.2.1.sub_const 1) ht.2.2.2)
    (by
      filter_upwards [hderivC] with t ht
      apply (((ht.1.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
        ((ht.2.1.sub_const 1).mul (Real.hasDerivAt_sin t))).congr_deriv
      unfold innerCornerDX supportP supportQ
      ring)
    (by
      filter_upwards [hderivC] with t ht
      apply (((ht.1.sub_const 1).mul (Real.hasDerivAt_sin t)).add
        ((ht.2.1.sub_const 1).mul (Real.hasDerivAt_cos t))).congr_deriv
      unfold innerCornerDY supportP supportQ
      ring)
    (by
      filter_upwards [hderivB] with t ht
      exact hasDerivAt_supportPoint_fst (ht.1.sub_const 1) ht.2.2.1)
    (by
      filter_upwards [hderivB] with t ht
      exact hasDerivAt_supportPoint_snd (ht.1.sub_const 1) ht.2.2.1)
    hDXi hDYi (hCXc.intervalIntegrable _ _) (hCYc.intervalIntegrable _ _)
    hBXi hBYi hN hgraphD hgraphC hgraphB
    (innerCorner_eq_secondTangent_of_momentum_zero hqzero).symm
    (innerCorner_eq_firstTangent_of_momentum_zero hpzero) hDzero hBzero
  have hdetD : (∫ t in (0 : ℝ)..d, coordDet (secondTangentPoint g gD t)
      (companionSupportPointDX (fun s => g s - 1) gDD t,
        companionSupportPointDY (fun s => g s - 1) gDD t)) =
      ∫ t in (0 : ℝ)..d, (g t - 1) * (g t - 1 + gDD t) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact coordDet_companionSupportPoint (fun s => g s - 1) gD gDD t
  have hdetB : (∫ t in b..(Real.pi / 2), coordDet (firstTangentPoint f fD t)
      (supportPointDX (fun s => f s - 1) fDD t,
        supportPointDY (fun s => f s - 1) fDD t)) =
      ∫ t in b..(Real.pi / 2), (f t - 1) * (f t - 1 + fDD t) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact coordDet_supportPoint (fun s => f s - 1) fD fDD t
  have hdetC : (∫ t in b..d, coordDet (innerCornerPoint f g t)
      (innerCornerDX f g fD gD t, innerCornerDY f g fD gD t)) =
      ∫ t in b..d, cornerDensity f g fD gD t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact coordDet_innerCorner f g fD gD t
  rw [hdetD, hdetC, hdetB] at hgraphs
  simp only [secondTangentPoint, companionSupportPoint_coordinates, firstTangentPoint,
    Reference.supportPoint, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, mul_zero, mul_one, zero_sub, zero_mul] at hgraphs
  have hBint := integral_firstTangent_density_ac hbL hf hg hfD hgD
    (hfAC.mono hsubB) (hgAC.mono hsubB) (hfDAC.mono hsubB)
    (hderivB.mono fun _ ht => ht.1) (hderivB.mono fun _ ht => ht.2.1)
    (hderivB.mono fun _ ht => ht.2.2.1) hfDD'
  have hDint := integral_secondTangent_density_ac h0d hf hg hfD hgD
    (hfAC.mono hsubD) (hgAC.mono hsubD) (hgDAC.mono hsubD)
    (hderivD.mono fun _ ht => ht.1) (hderivD.mono fun _ ht => ht.2.1)
    (hderivD.mono fun _ ht => ht.2.2.2) hgDD'
  simp only [firstMomentumPrimitive, hFtop, hpzero, sub_self, zero_mul,
    mul_zero, add_zero, sub_zero] at hBint
  simp only [secondMomentumPrimitive, hGtop, hqzero, sub_self, zero_mul,
    mul_zero, add_zero, sub_zero] at hDint
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ
    fun_prop
  have hsplit0 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 d) (hc.intervalIntegrable d (Real.pi / 2))
  have hsplitb := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable b d) (hc.intervalIntegrable d (Real.pi / 2))
  linarith

end AmbidextrousSofa
