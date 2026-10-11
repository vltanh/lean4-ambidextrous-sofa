module

public import AmbidextrousSofa.Measure.SignedRoofIntegral
public import AmbidextrousSofa.Measure.SupportAreaAC

@[expose] public section

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
  have h0d : 0 ≤ d := hb0.trans hbd
  have hbL : b ≤ Real.pi / 2 := hbd.trans hdL
  have hsubD : uIcc 0 d ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le h0d hdL)
  have hsubC : uIcc b d ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le hb0 hbL) (mem_uIcc_of_le h0d hdL)
  have hsubB : uIcc b (Real.pi / 2) ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le hb0 hbL) right_mem_uIcc
  have hderivD := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hdL) hderiv
  have hderivC := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hb0 hdL) hderiv
  have hderivB := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hb0 le_rfl) hderiv
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 (Real.pi / 2) :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hsin : AbsolutelyContinuousOnInterval Real.sin 0 (Real.pi / 2) :=
    Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval
  have hcos : AbsolutelyContinuousOnInterval Real.cos 0 (Real.pi / 2) :=
    Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval
  have hBac :
      AbsolutelyContinuousOnInterval (fun t => (firstTangentPoint f fD t).1) 0 (Real.pi / 2) ∧
        AbsolutelyContinuousOnInterval (fun t => (firstTangentPoint f fD t).2) 0 (Real.pi / 2) :=
    absolutelyContinuousOnInterval_supportPoint (hfAC.sub hconst) hfDAC
  have hDac :
      AbsolutelyContinuousOnInterval (fun t => (secondTangentPoint g gD t).1) 0 (Real.pi / 2) ∧
        AbsolutelyContinuousOnInterval (fun t => (secondTangentPoint g gD t).2) 0 (Real.pi / 2) :=
    absolutelyContinuousOnInterval_companionSupportPoint (hgAC.sub hconst) hgDAC
  have hCXac : AbsolutelyContinuousOnInterval (fun t => (innerCornerPoint f g t).1)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hcos).sub ((hgAC.sub hconst).mul hsin)
  have hCYac : AbsolutelyContinuousOnInterval (fun t => (innerCornerPoint f g t).2)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hsin).add ((hgAC.sub hconst).mul hcos)
  have hp : Continuous (supportP fD g) := (hfD.sub hg).add continuous_const
  have hq : Continuous (supportQ gD f) := (hgD.add hf).sub continuous_const
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ; fun_prop
  have hCX : Continuous (innerCornerDX f g fD gD) := by
    unfold innerCornerDX supportP supportQ; fun_prop
  have hCY : Continuous (innerCornerDY f g fD gD) := by
    unfold innerCornerDY supportP supportQ; fun_prop
  have hfDD' := hfDD.mono_set hsubB
  have hgDD' := hgDD.mono_set hsubD
  have hBrho : IntervalIntegrable (fun t => f t - 1 + fDD t) volume b (Real.pi / 2) :=
    ((hf.sub continuous_const).intervalIntegrable _ _).add hfDD'
  have hDrho : IntervalIntegrable (fun t => g t - 1 + gDD t) volume 0 d :=
    ((hg.sub continuous_const).intervalIntegrable _ _).add hgDD'
  -- The three arcs as graphs of `N`; the corner arc is traversed in reverse.
  have hDi := twice_integral_graph_parametrization_ac h0d (hDac.1.mono hsubD) (hDac.2.mono hsubD)
    (XD := companionSupportPointDX (fun s => g s - 1) gDD)
    (YD := companionSupportPointDY (fun s => g s - 1) gDD)
    (hderivD.mono fun t ht => hasDerivAt_companionSupportPoint_fst (ht.2.1.sub_const 1) ht.2.2.2)
    (hderivD.mono fun t ht => hasDerivAt_companionSupportPoint_snd (ht.2.1.sub_const 1) ht.2.2.2)
    (hDrho.neg.mul_continuousOn Real.continuous_cos.continuousOn)
    (hDrho.neg.mul_continuousOn Real.continuous_sin.continuousOn) hN.continuousOn hgraphD
  have hCi := twice_integral_graph_parametrization_ac hbd (hCXac.mono hsubC) (hCYac.mono hsubC)
    (XD := innerCornerDX f g fD gD) (YD := innerCornerDY f g fD gD)
    (hderivC.mono fun t ht => (((ht.1.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
      ((ht.2.1.sub_const 1).mul (Real.hasDerivAt_sin t))).congr_deriv
      (by simp only [innerCornerDX, supportP, supportQ]; ring))
    (hderivC.mono fun t ht => (((ht.1.sub_const 1).mul (Real.hasDerivAt_sin t)).add
      ((ht.2.1.sub_const 1).mul (Real.hasDerivAt_cos t))).congr_deriv
      (by simp only [innerCornerDY, supportP, supportQ]; ring))
    (hCX.intervalIntegrable _ _) (hCY.intervalIntegrable _ _) hN.continuousOn hgraphC
  have hBi := twice_integral_graph_parametrization_ac hbL (hBac.1.mono hsubB) (hBac.2.mono hsubB)
    (XD := supportPointDX (fun s => f s - 1) fDD) (YD := supportPointDY (fun s => f s - 1) fDD)
    (hderivB.mono fun t ht => hasDerivAt_supportPoint_fst (ht.1.sub_const 1) ht.2.2.1)
    (hderivB.mono fun t ht => hasDerivAt_supportPoint_snd (ht.1.sub_const 1) ht.2.2.1)
    (hBrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hBrho.mul_continuousOn Real.continuous_cos.continuousOn) hN.continuousOn hgraphB
  rw [← innerCorner_eq_secondTangent_of_momentum_zero hqzero] at hDi
  rw [← innerCorner_eq_firstTangent_of_momentum_zero hpzero] at hBi
  simp only [Prod.mk.eta, secondTangentPoint, firstTangentPoint, coordDet_companionSupportPoint,
    coordDet_supportPoint, coordDet_innerCorner] at hDi hCi hBi
  simp only [companionSupportPoint_coordinates, Reference.supportPoint, hFtop, hGtop,
    Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, sub_self, mul_zero,
    mul_one, zero_sub, sub_zero, add_zero] at hDi hBi
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hN.intervalIntegrable (μ := volume) (-gD 0) (innerCornerPoint f g b).1)
    (hN.intervalIntegrable (innerCornerPoint f g b).1 (innerCornerPoint f g d).1)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (hN.intervalIntegrable (μ := volume) (-gD 0) (innerCornerPoint f g b).1)
    (hN.intervalIntegrable (innerCornerPoint f g b).1 (-fD (Real.pi / 2)))
  have hB := integral_density_of_identity (firstTangent_density_identity f g fD gD fDD) hc hp
    (((hfD.mul hp).intervalIntegrable _ _).add
      ((hfDD'.sub (hgD.intervalIntegrable _ _)).continuousOn_mul
        (hf.sub continuous_const).continuousOn))
    (integral_eq_sub_of_ac_of_ae_hasDerivAt hbL (E := firstMomentumPrimitive f g fD)
      (((hfAC.sub hconst).mul ((hfDAC.sub hgAC).add hconst)).mono hsubB)
      (hderivB.mono fun t ht => (ht.1.sub_const 1).mul ((ht.2.2.1.sub ht.2.1).add_const 1)))
  have hD := integral_density_of_identity (secondTangent_density_identity f g fD gD gDD) hc hq
    (((hgD.mul hq).intervalIntegrable _ _).add
      ((hgDD'.add (hfD.intervalIntegrable _ _)).continuousOn_mul
        (hg.sub continuous_const).continuousOn))
    (integral_eq_sub_of_ac_of_ae_hasDerivAt h0d (E := secondMomentumPrimitive f g gD)
      (((hgAC.sub hconst).mul ((hgDAC.add hfAC).sub hconst)).mono hsubD)
      (hderivD.mono fun t ht => (ht.2.1.sub_const 1).mul ((ht.2.2.2.add ht.1).sub_const 1)))
  simp only [firstMomentumPrimitive, secondMomentumPrimitive, hFtop, hGtop, hpzero, hqzero,
    sub_self, zero_mul, mul_zero, add_zero] at hB hD
  have hsplit0 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 d) (hc.intervalIntegrable d (Real.pi / 2))
  have hsplitb := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) b d) (hc.intervalIntegrable d (Real.pi / 2))
  linarith

end AmbidextrousSofa
