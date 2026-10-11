module

public import AmbidextrousSofa.Analysis.TiltedInitialCircle
public import AmbidextrousSofa.Analysis.TiltedEndpointLeakage
public import AmbidextrousSofa.Analysis.HorizontalNicheGraphs

@[expose] public section

/-!
# The actual first-unit tangency and its middle crossing

The first tangent locus is monotone in abscissa and antitone in height
under the actual first-wing unit-density bound. Its closed traces retain
the literal top endpoint. A source-box estimate makes the first momentum
strictly negative whenever that tangency has reached the right middle
endpoint; this estimate does not use any companion curvature bound.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

namespace Analysis

/-- A strict source-box sign margin at every width above one half. On
small cosines a quadratic lower bound for the sine pays the entire linear
height term; rational boxes cover the other cosines. -/
theorem firstUnit_source_box_margin_of_half_lt {C h k s : ℝ}
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hk0 : 0 ≤ k) (hkC : k ≤ C) (hs0 : 0 ≤ s) (hcircle : s ^ 2 + k ^ 2 = 1) :
    1 - (2 * C + k) * s + h * k < 0 := by
  have hhk := mul_le_mul_of_nonneg_right hh hk0
  have hcoef : 0 ≤ 2 * C + k := by linarith only [hC0, hk0]
  rcases le_or_gt k (1 / 2) with hk | hk
  · have hr0 : 0 < 1 - 2 / 3 * k ^ 2 := by nlinarith only [hk, hk0]
    have hs : 1 - 2 / 3 * k ^ 2 ≤ s := (sq_le_sq₀ hr0.le hs0).mp (by
      nlinarith only [hcircle, mul_nonneg (sq_nonneg k)
        (show 0 ≤ 3 - 4 * k ^ 2 by nlinarith only [hk, hk0])])
    nlinarith only [mul_le_mul_of_nonneg_left hs hcoef, hhk, hk0,
      mul_pos (by linarith only [hC0] : 0 < 2 * C - 1) hr0,
      mul_nonneg hk0 (sub_nonneg.mpr hk), mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hk)]
  have hbox (c K : ℝ) (hc : 0 ≤ c) (hK : k ≤ K) (hcK : c ^ 2 + K ^ 2 ≤ 1) :
      (2 * C + k) * c ≤ (2 * C + k) * s :=
    mul_le_mul_of_nonneg_left (by nlinarith only [hc, hK, hcK, hcircle, hs0, hk0]) hcoef
  rcases le_or_gt C (3 / 5) with hC | hC
  · nlinarith only [hhk, hk, hC0, hbox (4 / 5) (3 / 5) (by norm_num) (hkC.trans hC) (by norm_num)]
  rcases le_or_gt C (2 / 3) with hC' | hC'
  · nlinarith only [hhk, hk, hC,
      hbox (37 / 50) (2 / 3) (by norm_num) (hkC.trans hC') (by norm_num)]
  · nlinarith only [hhk, hk, hC',
      hbox (2 / 3) (37 / 50) (by norm_num) (hkC.trans hC1) (by norm_num)]

end Analysis

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "B" => firstTangentPoint (F).f (F).fD
local notation "D" => secondTangentPoint (F).g (F).gD
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_tangent_traces {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) :
    B 0 = (2 * C - 1, capRoof U (horizontalRight U)) ∧
      B (Real.pi / 2) = ((MovingSofaOptimality.vminus U (Real.pi / 2)).1, 0) ∧
      D 0 = (-C, -h) ∧
      D (Real.pi / 2) = (1 - 2 * C, capRoof U (horizontalLeft U)) ∧
      p (Real.pi / 2) = 1 - 2 * C - (MovingSofaOptimality.vminus U (Real.pi / 2)).1 ∧
      q (Real.pi / 2) = -capRoof U (horizontalLeft U) := by
  obtain ⟨hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  have hj : horizontalLeft U + capWidth U / 4 = -C := by rw [capWidth, hl, hr]; ring
  rw [hj] at hg0 hgD0
  simp only [firstTangentPoint, secondTangentPoint, Reference.supportPoint,
    companionSupportPoint_coordinates, supportP, supportQ, hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL,
    hgDL, hlow, hl, hr, hheight, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

theorem fullTiltedSupportQuarterPair_first_tangent_order
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    MonotoneOn (fun t => (B t).1) (Icc 0 (Real.pi / 2)) ∧
      AntitoneOn (fun t => (B t).2) (Icc 0 (Real.pi / 2)) := by
  obtain ⟨hBx, hBy, -, -, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  constructor
  · apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hBx hL
    filter_upwards [hderiv, hunit, ae_restrict_mem measurableSet_Ioo] with t hd hu ht
    exact ⟨hd.1, mul_nonneg (sub_nonneg.mpr hu)
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith only [ht.2, Real.pi_pos]))⟩
  · have := absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hBy.neg hL (by
      filter_upwards [hderiv, hunit, ae_restrict_mem measurableSet_Ioo] with t hd hu ht
      exact ⟨hd.2.1.neg, neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu)
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith only [ht.1, Real.pi_pos])
          ht.2.le))⟩)
    exact fun s hs t ht hst => neg_le_neg_iff.mp (this hs ht hst)

/-- The source point of `B` lies in the original cap. The low middle
point lies in the literal cut. These two facts supply a strict sign
margin even when the companion tangent folds. -/
theorem fullTiltedSupportQuarterPair_first_momentum_neg_after_middle {C h t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hlow : capRoof U (-C) = 1 - h)
    (ht : t ∈ Icc 0 (Real.pi / 2)) (hB : C ≤ (B t).1) :
    Real.cos t ≤ C ∧ p t < 0 := by
  have hP := (fullTiltedSupportQuarterPair_points_mem hU hm haffine hρ hρ0 hρK heq).1 t ht
  have hPx := (hU.isCap.fst_mem_Icc hP).2
  have hPy := (hU.isCap.inStrip hP).2
  rw [hr] at hPx
  simp only [firstTangentPoint, Reference.supportPoint] at hB hPx hPy
  have hs : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith only [ht.1, Real.pi_pos]) ht.2
  have hk : Real.cos t ≤ C := by linarith only [hB, hPx]
  have hproj : -C ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
    constructor <;> linarith only [hC0]
  have hg := coordDot_le_support (hU.isCap.leftCompanionCap hproj).isCompact
    (hlow ▸ hU.isCap.rightRoof_mem_leftCompanionCap hproj) (companionNormal t)
  have hgF : C * Real.sin t + (1 - h) * Real.cos t ≤ (F).g t := by
    change _ ≤ angleSupport (leftCompanionCap U
      (horizontalLeft U + capWidth U / 4)) (t + Real.pi / 2)
    rw [show horizontalLeft U + capWidth U / 4 = -C by rw [capWidth, hl, hr]; ring,
      angleSupport, ← companionNormal_eq_unitNormal]
    simpa only [coordDot, companionNormal, neg_mul, mul_neg, neg_neg] using hg
  refine ⟨hk, lt_of_le_of_lt ?_ (Analysis.firstUnit_source_box_margin_of_half_lt
    hC0 hC1 hh hc hk hs (Real.sin_sq_add_cos_sq t))⟩
  unfold supportP
  nlinarith only [hgF, mul_le_mul_of_nonneg_right hB hs, mul_le_mul_of_nonneg_right hPy hc,
    congrArg ((F).fD t * ·) (Real.sin_sq_add_cos_sq t)]

theorem fullTiltedSupportQuarterPair_exists_first_middle_crossing {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (htop : C < (MovingSofaOptimality.vminus U (Real.pi / 2)).1)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∃ β ∈ Ioo 0 (Real.pi / 2),
      (B β).1 = C ∧
      (∀ t ∈ Ico 0 β, (B t).1 < C) ∧
      (∀ t ∈ Icc β (Real.pi / 2), C ≤ (B t).1) ∧
      Real.arccos C ≤ β ∧ 3 / 5 ≤ Real.sin β ∧
      p β < 0 ∧ 0 ≤ (B β).2 := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hB0, hBL, -, -, -, -⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow
  have hcont : ContinuousOn (fun t => C - (B t).1) (Icc 0 (Real.pi / 2)) :=
    uIcc_of_le hL.le ▸ continuousOn_const.sub (fullTiltedSupportQuarterPair_tangent_calculus
      hU hm haffine hρ hρ0 hρK heq).1.continuousOn
  obtain ⟨β, hβ, heqβ, hbefore⟩ := exists_first_level_crossing hL hcont
    (show (0 : ℝ) < C - (B 0).1 by simp only [hB0]; linarith only [hC1])
    (show C - (B (Real.pi / 2)).1 ≤ 0 by simp only [hBL]; linarith only [htop])
  have hβx : (B β).1 = C := by linarith only [heqβ]
  have hβL : β < Real.pi / 2 :=
    hβ.2.lt_of_ne (by rintro rfl; simp only [hBL] at hβx; exact htop.ne' hβx)
  have horder := fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit
  have hgeom := fullTiltedSupportQuarterPair_first_momentum_neg_after_middle
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hlow ⟨hβ.1.le, hβ.2⟩ hβx.ge
  have hy := horder.2 ⟨hβ.1.le, hβ.2⟩ ⟨hL.le, le_rfl⟩ hβ.2
  simp only [hBL] at hy
  refine ⟨β, ⟨hβ.1, hβL⟩, hβx, fun t ht => by linarith only [hbefore t ht],
    fun t ht => hβx ▸ horder.1 ⟨hβ.1.le, hβ.2⟩ ⟨hβ.1.le.trans ht.1, ht.2⟩ ht.1,
    (Real.arccos_le_arccos hgeom.1).trans_eq
      (Real.arccos_cos hβ.1.le (by linarith only [hβ.2, Real.pi_pos])), ?_, hgeom.2, hy⟩
  nlinarith only [Real.sin_sq_add_cos_sq β, hgeom.1, hC1,
    Real.sin_nonneg_of_nonneg_of_le_pi hβ.1.le (by linarith only [hβ.2, Real.pi_pos]),
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith only [hβ.1, Real.pi_pos]) hβ.2]

end ActualPair

end AmbidextrousSofa
