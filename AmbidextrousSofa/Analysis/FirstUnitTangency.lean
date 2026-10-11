module

public import AmbidextrousSofa.Analysis.TiltedInitialCircle
public import AmbidextrousSofa.Analysis.TiltedEndpointLeakage
public import AmbidextrousSofa.Analysis.HorizontalNicheGraphs

@[expose] public section

/-!
# The first-unit setting and the actual first tangency

`FirstUnitSetting` collects the hypotheses of the first-unit width range: the horizontal
projection is `[-2C, 2C]`, the affine middle roof rises from `1 - h` to `1`, and the first
density obeys the sharp source bound and is at most one. The low-wing cut at `-C` is then a
cap of height `1 - h` whose left endpoint lies strictly above the floor.

Under the unit first density, the first tangent locus is monotone in abscissa and antitone
in height, and it stays above the floor. Its closed traces retain the literal top endpoint.
A source-box estimate makes the first momentum strictly negative whenever that tangency has
reached the right middle endpoint; this estimate does not use any companion curvature bound.
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

/-- The low-wing cut at `-C` of a positively tilted full maximum with horizontal projection
`[-2C, 2C]`: both middle endpoints lie in the projection, the cut is a cap of height `1 - h`
with top point `(-C, 1 - h)`, and its left endpoint lies strictly above the floor. -/
theorem IsFullCapMaximizer.low_wing_cut {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C) (hC : 0 < C)
    (hmpos : 0 < m) (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    -C ∈ horizontalProjection U ∧ C ∈ horizontalProjection U ∧
      IsDownwardCap (leftCompanionCap U (-C)) ∧ capHeight (leftCompanionCap U (-C)) = 1 - h ∧
      MovingSofaOptimality.vplus (leftCompanionCap U (-C)) (Real.pi / 2) = (-C, 1 - h) ∧
      0 < capRoof (leftCompanionCap U (-C)) (horizontalLeft (leftCompanionCap U (-C))) := by
  have hP := hU.isCap.horizontalProjection_eq_Icc
  have ha : -C ∈ horizontalProjection U := by rw [hP, hl, hr]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hP, hl, hr]; constructor <;> linarith only [hC]
  have htop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (by linarith only [hC])
    hmpos ((centered_quarter_points hl hr).2.2 ▸ haffine)
  rw [hlow] at htop
  refine ⟨ha, hb, hU.isCap.leftCompanionCap ha, htop.1, htop.2, ?_⟩
  have hab : horizontalLeft U ≤ -C := by rw [hl]; linarith only [hC]
  rw [horizontalLeft_leftCompanionCap hU.isCap ha, show capRoof (leftCompanionCap U (-C))
    (horizontalLeft U) = capRoof U (horizontalLeft U) from capRoof_horizontalCut hU.isCap hab
      (hP ▸ Icc_subset_Icc le_rfl (hP ▸ ha).2) ⟨le_rfl, hab⟩]
  exact (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2

/-- The hypotheses of the first-unit width range for a tilted full maximum `U` whose middle
roof is affine with slope `m`: the horizontal projection is `[-2C, 2C]`, the middle roof rises
from `1 - h` to `1` with `C + m < 1`, and the first density `ρ` obeys the sharp source bound
and is at most one on the first quarter. -/
structure FirstUnitSetting (U : Set Plane) (m : ℝ) (ρ : ℝ → ℝ) (C h : ℝ) : Prop where
  hl : horizontalLeft U = -2 * C
  hr : horizontalRight U = 2 * C
  hC0 : 1 / 2 < C
  hC1 : C ≤ 37 / 50
  hh0 : 0 < h
  hh1 : h < 17 / 50
  hmpos : 0 < m
  hsmall : C + m < 1
  hheight : capHeight U = 1
  hlow : capRoof U (-C) = 1 - h
  hhigh : capRoof U C = 1
  hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t)
  hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1

namespace FirstUnitSetting

variable {U : Set Plane} {m : ℝ} {ρ : ℝ → ℝ} {C h : ℝ} (P : FirstUnitSetting U m ρ C h)
include P

theorem C_pos : 0 < C := by linarith only [P.hC0]

theorem left_quarter : horizontalLeft U + capWidth U / 4 = -C :=
  (centered_quarter_points P.hl P.hr).1

theorem right_quarter : horizontalRight U - capWidth U / 4 = C :=
  (centered_quarter_points P.hl P.hr).2.1

theorem middle : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C :=
  (centered_quarter_points P.hl P.hr).2.2

end FirstUnitSetting

/-! The notation for the actual support pair is opened in the sections whose variables are
the hypotheses `hU hm haffine hρ hρ0 hρK heq` it refers to: `F` is the pair, `B`, `D` and `Z`
its first tangent, second tangent and inner corner points, `p` and `q` its momenta, `v` the
companion density on the first quarter, and `V` the literal left cut. -/

namespace ActualPair

set_option quotPrecheck false
set_option hygiene false
scoped notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
scoped notation "B" => firstTangentPoint (F).f (F).fD
scoped notation "D" => secondTangentPoint (F).g (F).gD
scoped notation "Z" => innerCornerPoint (F).f (F).g
scoped notation "p" => supportP (F).fD (F).g
scoped notation "q" => supportQ (F).gD (F).f
scoped notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
scoped notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

end ActualPair

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

open scoped ActualPair

theorem fullTiltedSupportQuarterPair_tangent_traces {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) :
    B 0 = (2 * C - 1, capRoof U (horizontalRight U)) ∧
      B (Real.pi / 2) = ((MovingSofaOptimality.vminus U (Real.pi / 2)).1, 0) ∧
      D 0 = (-C, -h) ∧
      p (Real.pi / 2) = 1 - 2 * C - (MovingSofaOptimality.vminus U (Real.pi / 2)).1 ∧
      q (Real.pi / 2) = -capRoof U (horizontalLeft U) := by
  obtain ⟨hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  rw [capWidth, (centered_quarter_points hl hr).1] at hg0 hgD0
  simp only [firstTangentPoint, secondTangentPoint, Reference.supportPoint,
    companionSupportPoint_coordinates, supportP, supportQ, hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL,
    hgDL, hlow, hl, hr, hheight, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

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

theorem fullTiltedSupportQuarterPair_first_tangent_nonneg (hheight : capHeight U = 1)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 2)) : 0 ≤ (B t).2 := by
  have hfloor : (B (Real.pi / 2)).2 = 0 := by
    simp only [firstTangentPoint, Reference.supportPoint, hheight,
      (fullTiltedSupportQuarterPair_base_traces hU hm haffine hρ hρ0 hρK heq).2.2.1,
      Real.sin_pi_div_two, Real.cos_pi_div_two, sub_self, zero_mul, mul_zero, zero_add]
  exact hfloor.ge.trans ((fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).2 ht ⟨by positivity, le_rfl⟩ ht.2)

/-- Over a fixed abscissa the first wall moves with the slope given by the first tangent. -/
theorem fullTiltedSupportQuarterPair_first_wall_derivative {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (x : ℝ) :
    HasDerivAt (fun s => firstWall U s x) ((x - (B t).1) / Real.sin t ^ 2) t := by
  rw [fullTiltedSupportQuarterPair_first_tangency hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩]
  exact hU.isCap.hasDerivAt_firstWall_of_open_first_density hρ hρ0 hρK heq
    (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) ht x

/-- The source point of `B` lies in the original cap. The low middle
point lies in the literal cut. These two facts supply a strict sign
margin even when the companion tangent folds. -/
theorem FirstUnitSetting.first_momentum_neg_after_middle {C h t : ℝ}
    (P : FirstUnitSetting U m ρ C h) (ht : t ∈ Icc 0 (Real.pi / 2)) (hB : C ≤ (B t).1) :
    Real.cos t ≤ C ∧ p t < 0 := by
  have hP := (fullTiltedSupportQuarterPair_points_mem hU hm haffine hρ hρ0 hρK heq).1 t ht
  have hPx := (hU.isCap.fst_mem_Icc hP).2
  have hPy := (hU.isCap.inStrip hP).2
  rw [P.hr] at hPx
  simp only [firstTangentPoint, Reference.supportPoint] at hB hPx hPy
  have hs : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith only [ht.1, Real.pi_pos]) ht.2
  have hk : Real.cos t ≤ C := by linarith only [hB, hPx]
  obtain ⟨ha, -, hV, -⟩ := hU.low_wing_cut P.hl P.hr P.C_pos P.hmpos P.hheight P.hlow haffine
  have hg := coordDot_le_support hV.isCompact
    (P.hlow ▸ hU.isCap.rightRoof_mem_leftCompanionCap ha) (companionNormal t)
  have hgF : C * Real.sin t + (1 - h) * Real.cos t ≤ (F).g t := by
    change _ ≤ angleSupport (leftCompanionCap U
      (horizontalLeft U + capWidth U / 4)) (t + Real.pi / 2)
    rw [P.left_quarter, angleSupport, ← companionNormal_eq_unitNormal]
    simpa only [coordDot, companionNormal, neg_mul, mul_neg, neg_neg] using hg
  refine ⟨hk, lt_of_le_of_lt ?_ (Analysis.firstUnit_source_box_margin_of_half_lt
    P.hC0 P.hC1 P.hh1.le hc hk hs (Real.sin_sq_add_cos_sq t))⟩
  unfold supportP
  nlinarith only [hgF, mul_le_mul_of_nonneg_right hB hs, mul_le_mul_of_nonneg_right hPy hc,
    congrArg ((F).fD t * ·) (Real.sin_sq_add_cos_sq t)]

/-- The first tangent reaches the right middle endpoint at an interior angle `β`, after which
it stays to the right of it and the first momentum is negative. -/
theorem FirstUnitSetting.exists_first_middle_crossing {C h : ℝ} (P : FirstUnitSetting U m ρ C h)
    (htop : C < (MovingSofaOptimality.vminus U (Real.pi / 2)).1) :
    ∃ β ∈ Ioo 0 (Real.pi / 2), (B β).1 = C ∧ (∀ t ∈ Ico 0 β, (B t).1 < C) ∧
      (∀ t ∈ Icc β (Real.pi / 2), C ≤ (B t).1) ∧ 3 / 5 ≤ Real.sin β ∧ p β < 0 := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hB0, hBL, -⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq P.hl P.hr P.hmpos P.hheight P.hlow
  have hcont : ContinuousOn (fun t => C - (B t).1) (Icc 0 (Real.pi / 2)) :=
    uIcc_of_le hL.le ▸ continuousOn_const.sub (fullTiltedSupportQuarterPair_tangent_calculus
      hU hm haffine hρ hρ0 hρK heq).1.continuousOn
  obtain ⟨β, hβ, heqβ, hbefore⟩ := exists_first_level_crossing hL hcont
    (show (0 : ℝ) < C - (B 0).1 by simp only [hB0]; linarith only [P.hC1])
    (show C - (B (Real.pi / 2)).1 ≤ 0 by simp only [hBL]; linarith only [htop])
  have hβx : (B β).1 = C := by linarith only [heqβ]
  have hβL : β < Real.pi / 2 :=
    hβ.2.lt_of_ne (by rintro rfl; simp only [hBL] at hβx; exact htop.ne' hβx)
  have hgeom := P.first_momentum_neg_after_middle hU hm haffine hρ hρ0 hρK heq
    ⟨hβ.1.le, hβ.2⟩ hβx.ge
  refine ⟨β, ⟨hβ.1, hβL⟩, hβx, fun t ht => by linarith only [hbefore t ht],
    fun t ht => hβx ▸ (fullTiltedSupportQuarterPair_first_tangent_order
      hU hm haffine hρ hρ0 hρK heq P.hunit).1 ⟨hβ.1.le, hβ.2⟩ ⟨hβ.1.le.trans ht.1, ht.2⟩ ht.1,
    ?_, hgeom.2⟩
  nlinarith only [Real.sin_sq_add_cos_sq β, hgeom.1, P.hC1,
    Real.sin_nonneg_of_nonneg_of_le_pi hβ.1.le (by linarith only [hβ.2, Real.pi_pos]),
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith only [hβ.1, Real.pi_pos]) hβ.2]

end ActualPair

end AmbidextrousSofa
