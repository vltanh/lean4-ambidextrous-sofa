import AmbidextrousSofa.Analysis.TiltedInitialCircle
import AmbidextrousSofa.Analysis.TiltedEndpointLeakage
import AmbidextrousSofa.Analysis.HorizontalNicheGraphs

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
open scoped Topology

namespace AmbidextrousSofa

namespace Analysis

/-- A rational source-box margin on the remaining actual width range.
Splitting the cosine at one half avoids a convexity assumption on the
support or on the companion tangent locus. -/
theorem firstUnit_source_box_margin {C h k s : ℝ}
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hk0 : 0 ≤ k) (hkC : k ≤ C) (hs0 : 0 ≤ s) (hcircle : s ^ 2 + k ^ 2 = 1) :
    1 - (2 * C + k) * s + h * k < 0 := by
  have hCpos : 0 < C := by linarith only [hC0]
  have hhk := mul_le_mul_of_nonneg_right hh hk0
  by_cases hk : k ≤ 1 / 2
  · have hkSq := mul_nonneg (sub_nonneg.mpr hk)
      (show 0 ≤ 1 / 2 + k by linarith only [hk0])
    have hs : 4 / 5 ≤ s := by
      by_contra hnot
      have h := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
        (show 0 < 4 / 5 + s by linarith only [hs0])
      nlinarith only [hcircle, hkSq, h]
    have hprod := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 2 * C + k by linarith only [hCpos, hk0])
    nlinarith only [hprod, hhk, hC0, hk0]
  · have hkhalf : 1 / 2 < k := lt_of_not_ge hk
    have hkSq := mul_nonneg (sub_nonneg.mpr (hkC.trans hC1))
      (show 0 ≤ 37 / 50 + k by linarith only [hk0])
    have hs : 2 / 3 ≤ s := by
      by_contra hnot
      have h := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
        (show 0 < 2 / 3 + s by linarith only [hs0])
      nlinarith only [hcircle, hkSq, h]
    have hprod := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 2 * C + k by linarith only [hCpos, hk0])
    nlinarith only [hprod, hhk, hC0, hkhalf]

/-- The same strict sign margin extends down to every width above one
half. On small cosines a quadratic lower bound for the sine pays the
entire linear height term. Two rational boxes cover the other cosines. -/
theorem firstUnit_source_box_margin_of_half_lt {C h k s : ℝ}
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hk0 : 0 ≤ k) (hkC : k ≤ C) (hs0 : 0 ≤ s) (hcircle : s ^ 2 + k ^ 2 = 1) :
    1 - (2 * C + k) * s + h * k < 0 := by
  by_cases hC : 2 / 3 ≤ C
  · exact firstUnit_source_box_margin hC hC1 hh hk0 hkC hs0 hcircle
  have hCsmall : C ≤ 2 / 3 := (lt_of_not_ge hC).le
  have hhk := mul_le_mul_of_nonneg_right hh hk0
  have hcoef : 0 ≤ 2 * C + k := by linarith only [hC0, hk0]
  by_cases hk : k ≤ 1 / 2
  · have hkSq := mul_nonneg (sub_nonneg.mpr hk)
      (show 0 ≤ 1 / 2 + k by linarith only [hk0])
    have hr0 : 0 ≤ 1 - 2 / 3 * k ^ 2 := by nlinarith only [hkSq]
    have hpay := mul_nonneg (sq_nonneg k)
      (show 0 ≤ 3 - 4 * k ^ 2 by nlinarith only [hkSq])
    have hs : 1 - 2 / 3 * k ^ 2 ≤ s := by
      apply (sq_le_sq₀ hr0 hs0).mp
      nlinarith only [hcircle, hpay]
    have hprod := mul_le_mul_of_nonneg_left hs hcoef
    have hbox : 2 * C + k ≤ 99 / 50 := by linarith only [hC1, hk]
    have hquad := mul_le_mul_of_nonneg_right hbox (sq_nonneg k)
    have hksmall := mul_nonneg hk0 (sub_nonneg.mpr hk)
    have hlinear := mul_nonneg (show 0 ≤ 99 / 50 by norm_num) hksmall
    nlinarith only [hprod, hquad, hlinear, hhk, hC0]
  · have hkhalf : 1 / 2 < k := lt_of_not_ge hk
    by_cases hCshort : C ≤ 3 / 5
    · have hkSq := mul_nonneg (sub_nonneg.mpr (hkC.trans hCshort))
        (show 0 ≤ 3 / 5 + k by linarith only [hk0])
      have hs : 4 / 5 ≤ s := by
        apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 4 / 5) hs0).mp
        nlinarith only [hcircle, hkSq]
      have hprod := mul_le_mul_of_nonneg_left hs hcoef
      nlinarith only [hprod, hhk, hC0, hkhalf]
    · have hCthree : 3 / 5 < C := lt_of_not_ge hCshort
      have hkSq := mul_nonneg (sub_nonneg.mpr (hkC.trans hCsmall))
        (show 0 ≤ 2 / 3 + k by linarith only [hk0])
      have hs : 37 / 50 ≤ s := by
        apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 37 / 50) hs0).mp
        nlinarith only [hcircle, hkSq]
      have hprod := mul_le_mul_of_nonneg_left hs hcoef
      nlinarith only [hprod, hhk, hCthree, hkhalf]

end Analysis

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "B" => firstTangentPoint F.f F.fD
local notation "D" => secondTangentPoint F.g F.gD
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f

theorem fullTiltedSupportQuarterPair_tangent_traces {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) :
    B 0 = (2 * C - 1, capRoof U (horizontalRight U)) ∧
      B (Real.pi / 2) = ((Imported.vminus U (Real.pi / 2)).1, 0) ∧
      D 0 = (-C, -h) ∧
      D (Real.pi / 2) = (1 - 2 * C, capRoof U (horizontalLeft U)) ∧
      p (Real.pi / 2) = 1 - 2 * C - (Imported.vminus U (Real.pi / 2)).1 ∧
      q (Real.pi / 2) = -capRoof U (horizontalLeft U) := by
  obtain ⟨hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  have hj : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hl, hr]
    ring
  rw [hj, hlow] at hg0
  rw [hj] at hgD0
  rw [hl] at hgL
  rw [hr] at hf0
  rw [hheight] at hfL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [firstTangentPoint, Reference.supportPoint, hf0, hfD0,
      Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero, zero_add]
  · simp only [firstTangentPoint, Reference.supportPoint, hfL, hfDL,
      Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, sub_self,
      zero_sub, neg_neg, zero_add]
  · rw [secondTangentPoint, companionSupportPoint_coordinates]
    simp only [hg0, hgD0, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
      zero_sub, sub_zero, neg_neg]
    congr 1 <;> ring
  · rw [secondTangentPoint, companionSupportPoint_coordinates]
    simp only [hgL, hgDL, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_one, mul_zero, sub_zero, zero_sub, neg_neg]
    congr 1 <;> ring
  · unfold supportP
    rw [hfDL, hgL]
    ring
  · unfold supportQ
    rw [hgDL, hfL]
    ring

theorem fullTiltedSupportQuarterPair_first_tangent_order
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    MonotoneOn (fun t => (B t).1) (Icc 0 (Real.pi / 2)) ∧
      AntitoneOn (fun t => (B t).2) (Icc 0 (Real.pi / 2)) := by
  obtain ⟨hBx, hBy, _hDx, _hDy, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  constructor
  · apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hBx hL
    filter_upwards [hderiv, hunit, ae_restrict_mem measurableSet_Ioo] with t hd hu ht
    exact ⟨hd.1, mul_nonneg (sub_nonneg.mpr hu)
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith only [ht.2, Real.pi_pos]))⟩
  · have hneg : MonotoneOn (fun t => -(B t).2) (Icc 0 (Real.pi / 2)) := by
      apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hBy.neg hL
      filter_upwards [hderiv, hunit, ae_restrict_mem measurableSet_Ioo] with t hd hu ht
      exact ⟨hd.2.1.neg, neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hu) (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by linarith only [ht.1, Real.pi_pos]) ht.2.le))⟩
    intro s hs t ht hst
    exact neg_le_neg_iff.mp (hneg hs ht hst)

/-- The source point of `B` lies in the original cap. The low middle
point lies in the literal cut. These two facts supply a strict sign
margin even when the companion tangent folds. -/
theorem fullTiltedSupportQuarterPair_first_momentum_neg_after_middle {C h t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hlow : capRoof U (-C) = 1 - h)
    (ht : t ∈ Icc 0 (Real.pi / 2)) (hB : C ≤ (B t).1) :
    Real.cos t ≤ C ∧ p t < 0 := by
  let P := Reference.supportPoint F.f F.fD t
  have hP : P ∈ U :=
    (fullTiltedSupportQuarterPair_points_mem hU hm haffine hρ hρ0 hρK heq).1 t ht
  have hPx := (hU.isCap.fst_mem_Icc hP).2
  rw [hr] at hPx
  have hPy := (hU.isCap.inStrip hP).2
  have hBx : (B t).1 = P.1 - Real.cos t := by
    dsimp only [firstTangentPoint, Reference.supportPoint, P]
    ring
  have hk : Real.cos t ≤ C := by rw [hBx] at hB; linarith only [hB, hPx]
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [ht.1, Real.pi_pos]) ht.2
  have hfd : F.fD t = -P.1 * Real.sin t + P.2 * Real.cos t := by
    dsimp only [P, Reference.supportPoint]
    have hcircle := congrArg (fun r : ℝ => F.fD t * r) (Real.sin_sq_add_cos_sq t)
    nlinarith only [hcircle]
  have hj : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hproj : -C ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
      hl, hr]
    constructor <;> linarith only [hC0]
  have hlowP := hU.isCap.rightRoof_mem_leftCompanionCap hproj
  rw [hlow] at hlowP
  have hg := coordDot_le_support (hU.isCap.leftCompanionCap hproj).isCompact hlowP
    (companionNormal t)
  have hgF : C * Real.sin t + (1 - h) * Real.cos t ≤ F.g t := by
    change _ ≤ angleSupport (leftCompanionCap U
      (horizontalLeft U + capWidth U / 4)) (t + Real.pi / 2)
    rw [hj, angleSupport, ← companionNormal_eq_unitNormal]
    simpa only [coordDot, companionNormal, neg_mul, mul_neg, neg_neg] using hg
  have hX : C + Real.cos t ≤ P.1 := by rw [hBx] at hB; linarith only [hB]
  have hXs := mul_le_mul_of_nonneg_right hX hs
  have hYc := mul_le_mul_of_nonneg_right hPy hc
  have hupper : p t ≤ 1 - (2 * C + Real.cos t) * Real.sin t + h * Real.cos t := by
    unfold supportP
    rw [hfd]
    nlinarith only [hgF, hXs, hYc]
  exact ⟨hk, hupper.trans_lt
    (Analysis.firstUnit_source_box_margin_of_half_lt hC0 hC1 hh hc hk hs
      (Real.sin_sq_add_cos_sq t))⟩

theorem fullTiltedSupportQuarterPair_exists_first_middle_crossing {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (htop : C < (Imported.vminus U (Real.pi / 2)).1)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∃ β ∈ Ioo 0 (Real.pi / 2),
      (B β).1 = C ∧
      (∀ t ∈ Ico 0 β, (B t).1 < C) ∧
      (∀ t ∈ Icc β (Real.pi / 2), C ≤ (B t).1) ∧
      Real.arccos C ≤ β ∧ 3 / 5 ≤ Real.sin β ∧
      p β < 0 ∧ 0 ≤ (B β).2 := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hB0, hBL, _hD0, _hDL, _hpL, _hqL⟩ :=
    fullTiltedSupportQuarterPair_tangent_traces hU hm haffine hρ hρ0 hρK heq
      hl hr hmpos hheight hlow
  obtain ⟨hBx, hBy, _hDx, _hDy, _hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hcont : ContinuousOn (fun t => C - (B t).1) (Icc 0 (Real.pi / 2)) := by
    simpa only [uIcc_of_le hL.le] using continuousOn_const.sub hBx.continuousOn
  obtain ⟨β, hβ, heqβ, hbefore⟩ := exists_first_level_crossing hL hcont
    (show (0 : ℝ) < C - (B 0).1 by rw [hB0]; dsimp only [Prod.fst]; linarith only [hC1])
    (show C - (B (Real.pi / 2)).1 ≤ 0 by rw [hBL]; exact sub_nonpos.mpr htop.le)
  have hβx : (B β).1 = C := by linarith only [heqβ]
  have hβL : β < Real.pi / 2 := by
    apply lt_of_le_of_ne hβ.2
    intro heq
    rw [heq, hBL] at hβx
    exact htop.ne' hβx
  have horder := fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit
  have hgeom := fullTiltedSupportQuarterPair_first_momentum_neg_after_middle
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hlow ⟨hβ.1.le, hβ.2⟩ hβx.ge
  have hβacos : Real.arccos C ≤ β := by
    have h := Real.arccos_le_arccos hgeom.1
    rwa [Real.arccos_cos hβ.1.le (by linarith only [hβ.2, Real.pi_pos])] at h
  have hs0 : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ.1.le
    (by linarith only [hβ.2, Real.pi_pos])
  have hc0 : 0 ≤ Real.cos β := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [hβ.1, Real.pi_pos]) hβ.2
  have hsin : 3 / 5 ≤ Real.sin β := by
    have hkSq := mul_nonneg (sub_nonneg.mpr (hgeom.1.trans hC1))
      (show 0 ≤ 37 / 50 + Real.cos β by linarith only [hc0])
    by_contra hnot
    have h := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < 3 / 5 + Real.sin β by linarith only [hs0])
    nlinarith only [h, hkSq, Real.sin_sq_add_cos_sq β]
  have hy := horder.2 ⟨hβ.1.le, hβ.2⟩ ⟨hL.le, le_rfl⟩ hβ.2
  rw [hBL] at hy
  refine ⟨β, ⟨hβ.1, hβL⟩, hβx, ?_, ?_, hβacos, hsin, hgeom.2, hy⟩
  · intro t ht
    have h := hbefore t ht
    linarith only [h]
  · intro t ht
    rw [← hβx]
    exact horder.1 ⟨hβ.1.le, hβ.2⟩ ⟨hβ.1.le.trans ht.1, ht.2⟩ ht.1

end ActualPair

end AmbidextrousSofa
