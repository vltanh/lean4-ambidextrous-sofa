import AmbidextrousSofa.Measure.SignedRoof

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

theorem hasDerivWithinAt_innerCorner_fst {f g fD gD : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hg : HasDerivWithinAt g (gD t) (Ioi t) t) :
    HasDerivWithinAt (fun s => (innerCornerPoint f g s).1)
      (innerCornerDX f g fD gD t) (Ioi t) t := by
  unfold innerCornerPoint
  apply (((hf.sub_const 1).mul (Real.hasDerivAt_cos t).hasDerivWithinAt).sub
    ((hg.sub_const 1).mul (Real.hasDerivAt_sin t).hasDerivWithinAt)).congr_deriv
  unfold innerCornerDX supportP supportQ
  ring

theorem hasDerivWithinAt_innerCorner_snd {f g fD gD : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hg : HasDerivWithinAt g (gD t) (Ioi t) t) :
    HasDerivWithinAt (fun s => (innerCornerPoint f g s).2)
      (innerCornerDY f g fD gD t) (Ioi t) t := by
  unfold innerCornerPoint
  apply (((hf.sub_const 1).mul (Real.hasDerivAt_sin t).hasDerivWithinAt).add
    ((hg.sub_const 1).mul (Real.hasDerivAt_cos t).hasDerivWithinAt)).congr_deriv
  unfold innerCornerDY supportP supportQ
  ring

theorem coordDet_innerCorner (f g fD gD : ℝ → ℝ) (t : ℝ) :
    coordDet (innerCornerPoint f g t)
      (innerCornerDX f g fD gD t, innerCornerDY f g fD gD t) =
      cornerDensity f g fD gD t := by
  calc
    _ = cornerDensity f g fD gD t * (Real.sin t ^ 2 + Real.cos t ^ 2) := by
      unfold coordDet innerCornerPoint innerCornerDX innerCornerDY cornerDensity
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem innerCorner_eq_firstTangent_of_momentum_zero
    {f g fD : ℝ → ℝ} {t : ℝ} (hp : supportP fD g t = 0) :
    innerCornerPoint f g t = firstTangentPoint f fD t := by
  have h : fD t = g t - 1 := by unfold supportP at hp; linarith
  unfold innerCornerPoint firstTangentPoint Reference.supportPoint
  rw [h]

theorem innerCorner_eq_secondTangent_of_momentum_zero
    {f g gD : ℝ → ℝ} {t : ℝ} (hq : supportQ gD f t = 0) :
    innerCornerPoint f g t = secondTangentPoint g gD t := by
  have h : gD t = -(f t - 1) := by unfold supportQ at hq; linarith
  unfold secondTangentPoint
  rw [companionSupportPoint_coordinates]
  unfold innerCornerPoint
  rw [h]
  apply Prod.ext <;> dsimp <;> ring

theorem hasDerivWithinAt_firstMomentumPrimitive
    {f g fD gD fDD : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hg : HasDerivWithinAt g (gD t) (Ioi t) t)
    (hfD : HasDerivWithinAt fD (fDD t) (Ioi t) t) :
    HasDerivWithinAt (firstMomentumPrimitive f g fD)
      (firstMomentumDerivative f g fD gD fDD t) (Ioi t) t := by
  exact (hf.sub_const 1).mul ((hfD.sub hg).add_const 1)

theorem hasDerivWithinAt_secondMomentumPrimitive
    {f g fD gD gDD : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f (fD t) (Ioi t) t)
    (hg : HasDerivWithinAt g (gD t) (Ioi t) t)
    (hgD : HasDerivWithinAt gD (gDD t) (Ioi t) t) :
    HasDerivWithinAt (secondMomentumPrimitive f g gD)
      (secondMomentumDerivative f g fD gD gDD t) (Ioi t) t := by
  exact (hg.sub_const 1).mul ((hgD.add hf).sub_const 1)

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

theorem integral_firstTangent_density {a b : ℝ} {f g fD gD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hg : Continuous g)
    (hfD : Continuous fD) (hgD : Continuous gD)
    (hderivF : ∀ t ∈ Ioo a b, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hderivG : ∀ t ∈ Ioo a b, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecondF : ∀ t ∈ Ioo a b, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume a b) :
    (∫ t in a..b, (f t - 1) * (f t - 1 + fDD t)) =
      (∫ t in a..b, cornerDensity f g fD gD t) -
      (∫ t in a..b, supportP fD g t ^ 2) +
      firstMomentumPrimitive f g fD b - firstMomentumPrimitive f g fD a := by
  have hp : Continuous (supportP fD g) := (hfD.sub hg).add continuous_const
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ
    fun_prop
  have hprimitive : Continuous (firstMomentumPrimitive f g fD) :=
    (hf.sub continuous_const).mul hp
  have hd : IntervalIntegrable (firstMomentumDerivative f g fD gD fDD) volume a b :=
    ((hfD.mul hp).intervalIntegrable _ _).add
      ((hfDD.sub (hgD.intervalIntegrable _ _)).continuousOn_mul
        (hf.sub continuous_const).continuousOn)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    hprimitive.continuousOn
    (fun t ht => hasDerivWithinAt_firstMomentumPrimitive
      (hderivF t ht) (hderivG t ht) (hsecondF t ht)) hd
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

theorem integral_secondTangent_density {a b : ℝ} {f g fD gD gDD : ℝ → ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hg : Continuous g)
    (hfD : Continuous fD) (hgD : Continuous gD)
    (hderivF : ∀ t ∈ Ioo a b, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hderivG : ∀ t ∈ Ioo a b, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecondG : ∀ t ∈ Ioo a b, HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hgDD : IntervalIntegrable gDD volume a b) :
    (∫ t in a..b, (g t - 1) * (g t - 1 + gDD t)) =
      (∫ t in a..b, cornerDensity f g fD gD t) -
      (∫ t in a..b, supportQ gD f t ^ 2) +
      secondMomentumPrimitive f g gD b - secondMomentumPrimitive f g gD a := by
  have hq : Continuous (supportQ gD f) := (hgD.add hf).sub continuous_const
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ
    fun_prop
  have hprimitive : Continuous (secondMomentumPrimitive f g gD) :=
    (hg.sub continuous_const).mul hq
  have hd : IntervalIntegrable (secondMomentumDerivative f g fD gD gDD) volume a b :=
    ((hgD.mul hq).intervalIntegrable _ _).add
      ((hgDD.add (hfD.intervalIntegrable _ _)).continuousOn_mul
        (hg.sub continuous_const).continuousOn)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    hprimitive.continuousOn
    (fun t ht => hasDerivWithinAt_secondMomentumPrimitive
      (hderivF t ht) (hderivG t ht) (hsecondG t ht)) hd
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

/-- Three graph arcs with the middle one reversed. The identity does not
need a hidden injectivity, monotonicity, or disjointness assumption: it is an
identity of oriented integrals of the same actual graph. -/
theorem twice_integral_three_graph_arcs
    {a b d e : ℝ} {F : ℝ → ℝ} {P Q R : ℝ → Plane}
    {PX PY QX QY RX RY : ℝ → ℝ}
    (had : a ≤ d) (hbd : b ≤ d) (hbe : b ≤ e)
    (hP : Continuous P) (hQ : Continuous Q) (hR : Continuous R)
    (hPX : ∀ t ∈ Ioo a d, HasDerivWithinAt (fun s => (P s).1) (PX t) (Ioi t) t)
    (hPY : ∀ t ∈ Ioo a d, HasDerivWithinAt (fun s => (P s).2) (PY t) (Ioi t) t)
    (hQX : ∀ t ∈ Ioo b d, HasDerivWithinAt (fun s => (Q s).1) (QX t) (Ioi t) t)
    (hQY : ∀ t ∈ Ioo b d, HasDerivWithinAt (fun s => (Q s).2) (QY t) (Ioi t) t)
    (hRX : ∀ t ∈ Ioo b e, HasDerivWithinAt (fun s => (R s).1) (RX t) (Ioi t) t)
    (hRY : ∀ t ∈ Ioo b e, HasDerivWithinAt (fun s => (R s).2) (RY t) (Ioi t) t)
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
  have hpi := twice_integral_graph_parametrization had
    hP.fst.continuousOn hP.snd.continuousOn hPX hPY hPXi hPYi hF.continuousOn hgraphP
  have hqi := twice_integral_graph_parametrization hbd
    hQ.fst.continuousOn hQ.snd.continuousOn hQX hQY hQXi hQYi hF.continuousOn hgraphQ
  have hri := twice_integral_graph_parametrization hbe
    hR.fst.continuousOn hR.snd.continuousOn hRX hRY hRXi hRYi hF.continuousOn hgraphR
  rw [hPQ, hPzero, mul_zero] at hpi
  rw [← hQR, hRzero, mul_zero] at hri
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (P a).1 (Q b).1)
    (hF.intervalIntegrable (Q b).1 (Q d).1)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (P a).1 (Q b).1)
    (hF.intervalIntegrable (Q b).1 (R e).1)
  linarith

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
  have hBc : Continuous (firstTangentPoint f fD) := by
    unfold firstTangentPoint Reference.supportPoint
    fun_prop
  have hDc : Continuous (secondTangentPoint g gD) := by
    unfold secondTangentPoint Reference.companionSupportPoint Reference.supportPoint rotate
    fun_prop
  have hCc : Continuous (innerCornerPoint f g) := by
    unfold innerCornerPoint
    fun_prop
  have hCXc : Continuous (innerCornerDX f g fD gD) := by
    unfold innerCornerDX supportP supportQ
    fun_prop
  have hCYc : Continuous (innerCornerDY f g fD gD) := by
    unfold innerCornerDY supportP supportQ
    fun_prop
  have hBrho : IntervalIntegrable (fun t => f t - 1 + fDD t) volume b (Real.pi / 2) :=
    ((hf.sub continuous_const).intervalIntegrable _ _).add hfDD
  have hDrho : IntervalIntegrable (fun t => g t - 1 + gDD t) volume 0 d :=
    ((hg.sub continuous_const).intervalIntegrable _ _).add hgDD
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
  have hgraphs := twice_integral_three_graph_arcs h0d hbd hbL hDc hCc hBc
    (fun t _ => hasDerivWithinAt_companionSupportPoint_fst
      ((hderivG t).sub_const 1) (hsecondG t))
    (fun t _ => hasDerivWithinAt_companionSupportPoint_snd
      ((hderivG t).sub_const 1) (hsecondG t))
    (fun t _ => hasDerivWithinAt_innerCorner_fst (hderivF t) (hderivG t))
    (fun t _ => hasDerivWithinAt_innerCorner_snd (hderivF t) (hderivG t))
    (fun t _ => hasDerivWithinAt_supportPoint_fst ((hderivF t).sub_const 1) (hsecondF t))
    (fun t _ => hasDerivWithinAt_supportPoint_snd ((hderivF t).sub_const 1) (hsecondF t))
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
  have hBint := integral_firstTangent_density hbL hf hg hfD hgD
    (fun t _ => hderivF t) (fun t _ => hderivG t) (fun t _ => hsecondF t) hfDD
  have hDint := integral_secondTangent_density h0d hf hg hfD hgD
    (fun t _ => hderivF t) (fun t _ => hderivG t) (fun t _ => hsecondG t) hgDD
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
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hbL := hbd.trans hdL
  have h0d := hb0.trans hbd
  have hfDD' : IntervalIntegrable fDD volume b (Real.pi / 2) := by
    apply hfDD.mono_set
    simp only [uIcc_of_le hL, uIcc_of_le hbL]
    intro t ht
    exact ⟨hb0.trans ht.1, ht.2⟩
  have hgDD' : IntervalIntegrable gDD volume 0 d := by
    apply hgDD.mono_set
    simp only [uIcc_of_le hL, uIcc_of_le h0d]
    intro t ht
    exact ⟨ht.1, ht.2.trans hdL⟩
  apply signedRoof_integral_of_graphs hb0 hbd hdL hN hf hg hfD hgD
    hderivF hderivG hsecondF hsecondG hfDD' hgDD' hFtop hGtop hpzero hqzero
  · intro t ht
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨ht.1, ht.2.trans_le hdL⟩
    apply sweptNiche_secondTangent hU hFsupport hGsupport hGtop htL
      (hq t ⟨ht.1.le, ht.2.le⟩)
    intro s hs
    exact secondTangent_dominates_support hg hgD hderivG hsecondG hGcurv
      ⟨htL.1.le, htL.2.le⟩ hs
  · intro t ht
    have htL : t ∈ Ioo 0 (Real.pi / 2) :=
      ⟨hb0.trans_lt ht.1, ht.2.trans_le hdL⟩
    apply sweptNiche_innerCorner hU hFsupport hGsupport hFtop htL
      (hp t ⟨ht.1.le, htL.2.le⟩) (hq t ⟨htL.1.le, ht.2.le⟩)
    · intro s hs
      exact firstTangent_dominates_support hf hfD hderivF hsecondF hFcurv
        ⟨htL.1.le, htL.2.le⟩ hs
    · intro s hs
      exact secondTangent_dominates_support hg hgD hderivG hsecondG hGcurv
        ⟨htL.1.le, htL.2.le⟩ hs
  · intro t ht
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb0.trans_lt ht.1, ht.2⟩
    apply sweptNiche_firstTangent hU hFsupport hGsupport hFtop htL
      (hp t ⟨ht.1.le, ht.2.le⟩)
    intro s hs
    exact firstTangent_dominates_support hf hfD hderivF hsecondF hFcurv
      ⟨htL.1.le, htL.2.le⟩ hs

/-- A single sign switch changes a clipped square integral into its actual
active-interval integral. Endpoint values do not affect either integral. -/
theorem integral_min_sq_of_sign_switch {a b c : ℝ} {p : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hp : Continuous p)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ p t) (hright : ∀ t ∈ Icc b c, p t ≤ 0) :
    (∫ t in a..c, min (p t) 0 ^ 2) = ∫ t in b..c, p t ^ 2 := by
  have hclip : Continuous (fun t => min (p t) 0 ^ 2) :=
    (hp.min continuous_const).pow 2
  have hleftInt : (∫ t in a..b, min (p t) 0 ^ 2) = 0 := by
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        rw [min_eq_right (hleft t ht)]
        norm_num
      _ = 0 := by simp
  have hrightInt : (∫ t in b..c, min (p t) 0 ^ 2) = ∫ t in b..c, p t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hbc] at ht
    rw [min_eq_left (hright t ht)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hclip.intervalIntegrable a b) (hclip.intervalIntegrable b c)
  rw [hleftInt, hrightInt, zero_add] at hsplit
  exact hsplit.symm

theorem integral_max_sq_of_sign_switch {a b c : ℝ} {q : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hq : Continuous q)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ q t) (hright : ∀ t ∈ Icc b c, q t ≤ 0) :
    (∫ t in a..c, max (q t) 0 ^ 2) = ∫ t in a..b, q t ^ 2 := by
  have hclip : Continuous (fun t => max (q t) 0 ^ 2) :=
    (hq.max continuous_const).pow 2
  have hleftInt : (∫ t in a..b, max (q t) 0 ^ 2) = ∫ t in a..b, q t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    rw [max_eq_left (hleft t ht)]
  have hrightInt : (∫ t in b..c, max (q t) 0 ^ 2) = 0 := by
    calc
      _ = ∫ _t in b..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hbc] at ht
        rw [max_eq_right (hright t ht)]
        norm_num
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hclip.intervalIntegrable a b) (hclip.intervalIntegrable b c)
  rw [hleftInt, hrightInt, add_zero] at hsplit
  exact hsplit.symm

end AmbidextrousSofa
