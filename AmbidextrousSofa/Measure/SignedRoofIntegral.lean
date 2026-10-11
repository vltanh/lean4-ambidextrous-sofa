module

public import AmbidextrousSofa.Measure.SignedRoof

@[expose] public section

/-!
# The signed three-arc area formula

The second tangent arc, reversed corner arc, and first tangent arc are
integrated as actual graphs of one continuous function. Endpoint terms are
kept until the contact and zero-height identities cancel them. The resulting
formula is then applied to the complete angular niche using the global
exposure theorems in `SignedRoof`.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def innerCornerDX (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  supportP fD g t * Real.cos t - supportQ gD f t * Real.sin t

def innerCornerDY (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  supportP fD g t * Real.sin t + supportQ gD f t * Real.cos t

def cornerDensity (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - 1) * supportQ gD f t - (g t - 1) * supportP fD g t

def firstMomentumPrimitive (f g fD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - 1) * supportP fD g t

def secondMomentumPrimitive (f g gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (g t - 1) * supportQ gD f t

def firstMomentumDerivative (f g fD gD fDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  fD t * supportP fD g t + (f t - 1) * (fDD t - gD t)

def secondMomentumDerivative (f g fD gD gDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  gD t * supportQ gD f t + (g t - 1) * (gDD t + fD t)

theorem coordDet_innerCorner (f g fD gD : ℝ → ℝ) (t : ℝ) :
    coordDet (innerCornerPoint f g t)
      (innerCornerDX f g fD gD t, innerCornerDY f g fD gD t) =
      cornerDensity f g fD gD t := by
  simp only [coordDet, innerCornerPoint, innerCornerDX, innerCornerDY, cornerDensity]
  linear_combination ((f t - 1) * supportQ gD f t - (g t - 1) * supportP fD g t) *
    Real.sin_sq_add_cos_sq t

theorem innerCorner_eq_firstTangent_of_momentum_zero
    {f g fD : ℝ → ℝ} {t : ℝ} (hp : supportP fD g t = 0) :
    innerCornerPoint f g t = firstTangentPoint f fD t := by
  rw [innerCornerPoint, firstTangentPoint, Reference.supportPoint,
    show fD t = g t - 1 by unfold supportP at hp; linarith]

theorem innerCorner_eq_secondTangent_of_momentum_zero
    {f g gD : ℝ → ℝ} {t : ℝ} (hq : supportQ gD f t = 0) :
    innerCornerPoint f g t = secondTangentPoint g gD t := by
  rw [secondTangentPoint, companionSupportPoint_coordinates, innerCornerPoint,
    show gD t = -(f t - 1) by unfold supportQ at hq; linarith]
  ext <;> dsimp <;> ring

theorem firstTangent_density_identity (f g fD gD fDD : ℝ → ℝ) (t : ℝ) :
    (f t - 1) * (f t - 1 + fDD t) = cornerDensity f g fD gD t -
      supportP fD g t ^ 2 + firstMomentumDerivative f g fD gD fDD t := by
  unfold cornerDensity firstMomentumDerivative supportP supportQ
  ring

theorem secondTangent_density_identity (f g fD gD gDD : ℝ → ℝ) (t : ℝ) :
    (g t - 1) * (g t - 1 + gDD t) = cornerDensity f g fD gD t -
      supportQ gD f t ^ 2 + secondMomentumDerivative f g fD gD gDD t := by
  unfold cornerDensity secondMomentumDerivative supportP supportQ
  ring

/-- Integration of a density identity `L = c - P ^ 2 + M` whose correction `M` has an
explicit primitive. -/
theorem integral_density_of_identity {a b : ℝ} {L c P M Mp : ℝ → ℝ} (hab : a ≤ b)
    (hid : ∀ t, L t = c t - P t ^ 2 + M t) (hc : Continuous c) (hP : Continuous P)
    (hMp : Continuous Mp) (hM : ∀ t ∈ Ioo a b, HasDerivWithinAt Mp (M t) (Ioi t) t)
    (hMi : IntervalIntegrable M volume a b) :
    (∫ t in a..b, L t) = (∫ t in a..b, c t) - (∫ t in a..b, P t ^ 2) + Mp b - Mp a := by
  have hc' := hc.intervalIntegrable (μ := volume) a b
  have hP' : IntervalIntegrable (fun t => P t ^ 2) volume a b := (hP.pow 2).intervalIntegrable a b
  have hcP : IntervalIntegrable (fun t => c t - P t ^ 2) volume a b := hc'.sub hP'
  rw [intervalIntegral.integral_congr fun t _ => hid t, intervalIntegral.integral_add hcP hMi,
    intervalIntegral.integral_sub hc' hP',
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hMp.continuousOn hM hMi]
  ring

/-- Signed roof integration with actual graph identities on the three arcs.
The endpoint momentum equations join the arcs; the top support values give
zero heights at the two exterior endpoints. Curvature may jump. -/
theorem signedRoof_integral_of_graphs
    {b d : ℝ} {N f g fD gD fDD gDD : ℝ → ℝ}
    (hb0 : 0 ≤ b) (hbd : b ≤ d) (hdL : d ≤ Real.pi / 2)
    (hN : Continuous N) (hf : Continuous f) (hg : Continuous g)
    (hfD : Continuous fD) (hgD : Continuous gD)
    (hderivF : ∀ t, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hderivG : ∀ t, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecondF : ∀ t, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hsecondG : ∀ t, HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume b (Real.pi / 2))
    (hgDD : IntervalIntegrable gDD volume 0 d)
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
  have hp : Continuous (supportP fD g) := (hfD.sub hg).add continuous_const
  have hq : Continuous (supportQ gD f) := (hgD.add hf).sub continuous_const
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ; fun_prop
  have hCX : Continuous (innerCornerDX f g fD gD) := by
    unfold innerCornerDX supportP supportQ; fun_prop
  have hCY : Continuous (innerCornerDY f g fD gD) := by
    unfold innerCornerDY supportP supportQ; fun_prop
  have hBrho : IntervalIntegrable (fun t => f t - 1 + fDD t) volume b (Real.pi / 2) :=
    ((hf.sub continuous_const).intervalIntegrable _ _).add hfDD
  have hDrho : IntervalIntegrable (fun t => g t - 1 + gDD t) volume 0 d :=
    ((hg.sub continuous_const).intervalIntegrable _ _).add hgDD
  have hDc : Continuous (secondTangentPoint g gD) := by
    unfold secondTangentPoint Reference.companionSupportPoint Reference.supportPoint rotate
    fun_prop
  have hCc : Continuous (innerCornerPoint f g) := by unfold innerCornerPoint; fun_prop
  have hBc : Continuous (firstTangentPoint f fD) := by
    unfold firstTangentPoint Reference.supportPoint; fun_prop
  -- The three arcs as graphs of `N`; the corner arc is traversed in reverse.
  have hDi := twice_integral_graph_parametrization h0d hDc.fst.continuousOn hDc.snd.continuousOn
    (XD := companionSupportPointDX (fun s => g s - 1) gDD)
    (YD := companionSupportPointDY (fun s => g s - 1) gDD)
    (fun t _ => hasDerivWithinAt_companionSupportPoint_fst ((hderivG t).sub_const 1) (hsecondG t))
    (fun t _ => hasDerivWithinAt_companionSupportPoint_snd ((hderivG t).sub_const 1) (hsecondG t))
    (hDrho.neg.mul_continuousOn Real.continuous_cos.continuousOn)
    (hDrho.neg.mul_continuousOn Real.continuous_sin.continuousOn) hN.continuousOn hgraphD
  have hCi := twice_integral_graph_parametrization hbd hCc.fst.continuousOn hCc.snd.continuousOn
    (XD := innerCornerDX f g fD gD) (YD := innerCornerDY f g fD gD)
    (fun t _ => ((((hderivF t).sub_const 1).mul (Real.hasDerivAt_cos t).hasDerivWithinAt).sub
      (((hderivG t).sub_const 1).mul (Real.hasDerivAt_sin t).hasDerivWithinAt)).congr_deriv
      (by simp only [innerCornerDX, supportP, supportQ]; ring))
    (fun t _ => ((((hderivF t).sub_const 1).mul (Real.hasDerivAt_sin t).hasDerivWithinAt).add
      (((hderivG t).sub_const 1).mul (Real.hasDerivAt_cos t).hasDerivWithinAt)).congr_deriv
      (by simp only [innerCornerDY, supportP, supportQ]; ring))
    (hCX.intervalIntegrable _ _) (hCY.intervalIntegrable _ _) hN.continuousOn hgraphC
  have hBi := twice_integral_graph_parametrization hbL hBc.fst.continuousOn hBc.snd.continuousOn
    (XD := supportPointDX (fun s => f s - 1) fDD) (YD := supportPointDY (fun s => f s - 1) fDD)
    (fun t _ => hasDerivWithinAt_supportPoint_fst ((hderivF t).sub_const 1) (hsecondF t))
    (fun t _ => hasDerivWithinAt_supportPoint_snd ((hderivF t).sub_const 1) (hsecondF t))
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
  have hB := integral_density_of_identity hbL (firstTangent_density_identity f g fD gD fDD) hc hp
    (Mp := firstMomentumPrimitive f g fD) ((hf.sub continuous_const).mul hp)
    (fun t _ => ((hderivF t).sub_const 1).mul (((hsecondF t).sub (hderivG t)).add_const 1))
    (((hfD.mul hp).intervalIntegrable _ _).add
      ((hfDD.sub (hgD.intervalIntegrable _ _)).continuousOn_mul
        (hf.sub continuous_const).continuousOn))
  have hD := integral_density_of_identity h0d (secondTangent_density_identity f g fD gD gDD) hc hq
    (Mp := secondMomentumPrimitive f g gD) ((hg.sub continuous_const).mul hq)
    (fun t _ => ((hderivG t).sub_const 1).mul (((hsecondG t).add (hderivF t)).sub_const 1))
    (((hgD.mul hq).intervalIntegrable _ _).add
      ((hgDD.add (hfD.intervalIntegrable _ _)).continuousOn_mul
        (hg.sub continuous_const).continuousOn))
  simp only [firstMomentumPrimitive, secondMomentumPrimitive, hFtop, hGtop, hpzero, hqzero,
    sub_self, zero_mul, mul_zero, sub_zero] at hB hD
  have hsplit0 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 d) (hc.intervalIntegrable d (Real.pi / 2))
  have hsplitb := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) b d) (hc.intervalIntegrable d (Real.pi / 2))
  linarith

/-- The signed formula for the actual complete angular niche. The global
contact assertions are proved from realized supports, curvature at most one,
and the two momentum sign intervals. The conclusion contains the actual
integral of `sweptNiche`; no area certificate is an input. -/
theorem sweptNiche_integral_eq_signed_formula
    {U : Set Plane} (hU : IsCompact U) {b d : ℝ}
    {f g fD gD fDD gDD : ℝ → ℝ}
    (hb0 : 0 ≤ b) (hbd : b ≤ d) (hdL : d ≤ Real.pi / 2)
    (hN : Continuous (sweptNiche U (Real.pi / 2)))
    (hf : Continuous f) (hg : Continuous g) (hfD : Continuous fD) (hgD : Continuous gD)
    (hderivF : ∀ t, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hderivG : ∀ t, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecondF : ∀ t, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hsecondG : ∀ t, HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume 0 (Real.pi / 2))
    (hgDD : IntervalIntegrable gDD volume 0 (Real.pi / 2))
    (hFsupport : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hGsupport : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hFtop : f (Real.pi / 2) = 1) (hGtop : g 0 = 1)
    (hFcurv : ∀ t ∈ Icc 0 (Real.pi / 2), f t + fDD t ≤ 1)
    (hGcurv : ∀ t ∈ Icc 0 (Real.pi / 2), g t + gDD t ≤ 1)
    (hpzero : supportP fD g b = 0) (hqzero : supportQ gD f d = 0)
    (hp : ∀ t ∈ Icc b (Real.pi / 2), supportP fD g t ≤ 0)
    (hq : ∀ t ∈ Icc 0 d, 0 ≤ supportQ gD f t) :
    2 * (∫ x in (-gD 0)..(-fD (Real.pi / 2)), sweptNiche U (Real.pi / 2) x) =
      -(∫ t in (0 : ℝ)..(Real.pi / 2), cornerDensity f g fD gD t) +
      (∫ t in b..(Real.pi / 2), supportP fD g t ^ 2) +
      ∫ t in (0 : ℝ)..d, supportQ gD f t ^ 2 := by
  have hB : ∀ t ∈ Ioo 0 (Real.pi / 2), ∀ s ∈ Icc 0 (Real.pi / 2),
      f s - 1 ≤ coordDot (firstTangentPoint f fD t) (unitNormal s) := fun t ht s hs =>
    firstTangent_dominates_support hf hfD hderivF hsecondF hFcurv (Ioo_subset_Icc_self ht) hs
  have hD : ∀ t ∈ Ioo 0 (Real.pi / 2), ∀ s ∈ Icc 0 (Real.pi / 2),
      g s - 1 ≤ coordDot (secondTangentPoint g gD t) (companionNormal s) := fun t ht s hs =>
    secondTangent_dominates_support hg hgD hderivG hsecondG hGcurv (Ioo_subset_Icc_self ht) hs
  refine signedRoof_integral_of_graphs hb0 hbd hdL hN hf hg hfD hgD hderivF hderivG hsecondF
    hsecondG (hfDD.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hb0 (hbd.trans hdL)) right_mem_uIcc))
    (hgDD.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le (hb0.trans hbd) hdL)))
    hFtop hGtop hpzero hqzero (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨ht.1, ht.2.trans_le hdL⟩
    exact sweptNiche_secondTangent hU hFsupport hGsupport hGtop htL (hq t ⟨ht.1.le, ht.2.le⟩)
      (hD t htL)
  · have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb0.trans_lt ht.1, ht.2.trans_le hdL⟩
    exact sweptNiche_innerCorner hU hFsupport hGsupport hFtop htL (hp t ⟨ht.1.le, htL.2.le⟩)
      (hq t ⟨htL.1.le, ht.2.le⟩) (hB t htL) (hD t htL)
  · have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb0.trans_lt ht.1, ht.2⟩
    exact sweptNiche_firstTangent hU hFsupport hGsupport hFtop htL (hp t ⟨ht.1.le, ht.2.le⟩)
      (hB t htL)

theorem integral_split_of_eqOn {a b c : ℝ} {F G H : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hF : Continuous F) (hG : EqOn F G (Icc a b)) (hH : EqOn F H (Icc b c)) :
    (∫ t in a..c, F t) = (∫ t in a..b, G t) + ∫ t in b..c, H t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable a b)
    (hF.intervalIntegrable b c)]
  exact congrArg₂ (· + ·) (intervalIntegral.integral_congr (uIcc_of_le hab ▸ hG))
    (intervalIntegral.integral_congr (uIcc_of_le hbc ▸ hH))

/-- A single sign switch changes a clipped square integral into its actual
active-interval integral. Endpoint values do not affect either integral. -/
theorem integral_min_sq_of_sign_switch {a b c : ℝ} {p : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hp : Continuous p)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ p t) (hright : ∀ t ∈ Icc b c, p t ≤ 0) :
    (∫ t in a..c, min (p t) 0 ^ 2) = ∫ t in b..c, p t ^ 2 := by
  rw [integral_split_of_eqOn (F := fun t => min (p t) 0 ^ 2) (G := 0) (H := fun t => p t ^ 2)
    hab hbc ((hp.min continuous_const).pow 2) (fun t ht => by simp [min_eq_right (hleft t ht)])
    fun t ht => by simp [min_eq_left (hright t ht)]]
  simp

theorem integral_max_sq_of_sign_switch {a b c : ℝ} {q : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hq : Continuous q)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ q t) (hright : ∀ t ∈ Icc b c, q t ≤ 0) :
    (∫ t in a..c, max (q t) 0 ^ 2) = ∫ t in a..b, q t ^ 2 := by
  rw [integral_split_of_eqOn (F := fun t => max (q t) 0 ^ 2) (G := fun t => q t ^ 2) (H := 0)
    hab hbc ((hq.max continuous_const).pow 2) (fun t ht => by simp [max_eq_left (hleft t ht)])
    fun t ht => by simp [max_eq_right (hright t ht)]]
  simp

end AmbidextrousSofa
