module

public import AmbidextrousSofa.Analysis.FiniteSourceBalance
public import AmbidextrousSofa.Analysis.SupportHeightControl

@[expose] public section

/-!
# The stationary Green limit along the actual selected polygons

The two erosion moments control the absolute horizontal-normal moment of
the source defect. Its total mass is uniformly bounded. The support weight
minus one is bounded by that horizontal component plus the vanishing cap
height deficit. Consequently the actual finite weighted source defect tends
to zero. The exact finite Green identity then proves that the charged
polygon wing lengths tend to twice the actual limiting spatial score.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

theorem IsSelectedPolygon.abs_finiteSupportDefect_le {target U : Set Plane}
    {a b coefficient R : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) :
    |finiteSupportDefect U (normal (dyadic level)) (pairList (dyadic level)) none| ≤
      (R + 1) *
        (finiteRightMoment U (normal (dyadic level)) (pairList (dyadic level)) none +
          finiteLeftMoment U (normal (dyadic level)) (pairList (dyadic level)) none +
            2 * ∑ j, selectionDefect target U level coefficient j) +
      (1 - capHeight U) * ((4 * R + 12) * Real.pi +
        ∑ j, selectionDefect target U level coefficient j) := by
  have hgap : 0 ≤ 1 - capHeight U := sub_nonneg.mpr hU.isCap.capHeight_le_one
  have hpoint (j : SourceIndex (dyadic level)) :
      |support U (normal (dyadic level) j) - 1| ≤
        (R + 1) * |(normal (dyadic level) j).1| + (1 - capHeight U) :=
    hU.isCap.abs_support_sub_one_le_box hbox (normal_unit (dyadic level) j)
      (normal_snd_pos (dyadic level) j).le
  calc
    _ ≤ ∑ j : SourceIndex (dyadic level),
        |normalizedExposureDefect U (dyadic level) j| *
          |support U (normal (dyadic level) j) - 1| := by
      simpa only [finiteSupportDefect, normalizedExposureDefect, abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (f := fun j : SourceIndex (dyadic level) => normalizedExposureDefect U (dyadic level) j *
            (support U (normal (dyadic level) j) - 1)))
    _ ≤ ∑ j : SourceIndex (dyadic level),
        |normalizedExposureDefect U (dyadic level) j| *
          ((R + 1) * |(normal (dyadic level) j).1| + (1 - capHeight U)) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (abs_nonneg _))
    _ = (R + 1) * (∑ j : SourceIndex (dyadic level), |(normal (dyadic level) j).1| *
        |normalizedExposureDefect U (dyadic level) j|) +
      (1 - capHeight U) * ∑ j : SourceIndex (dyadic level),
        |normalizedExposureDefect U (dyadic level) j| := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (hU.sum_cos_abs_normalizedExposureDefect_le hc) (by linarith))
      (mul_le_mul_of_nonneg_left (hU.sum_abs_normalizedExposureDefect_le hc hR hbox) hgap)

theorem finiteSupportDefect_tendsto_zero_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteSupportDefect (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) := by
  let R : ℝ := |a| + |b| + 1
  have hR : 0 ≤ R := by positivity
  have hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 :=
    fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have herr := selectionDefect_sum_tendsto (level := level) hTarget.isCap hcap hc hrate hHausdorff
  have hH := hHausdorff.capHeight_tendsto hcap hTarget.isCap
  rw [hheight] at hH
  have hD := erosionMoments_tendsto_zero_of_canonical_maximum hTarget hheight haffine
    hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have hrhs : Tendsto (fun n =>
      (R + 1) *
        (finiteRightMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none +
          finiteLeftMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none +
            2 * ∑ j, selectionDefect target (U n) (level n) (coefficient n) j) +
      (1 - capHeight (U n)) * ((4 * R + 12) * Real.pi +
        ∑ j, selectionDefect target (U n) (level n) (coefficient n) j)) atTop (𝓝 0) := by
    simpa only [zero_add, add_zero, mul_zero, sub_self, zero_mul] using
      (((hD.1.add hD.2).add (herr.const_mul 2)).const_mul (R + 1)).add
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hH).mul
          ((tendsto_const_nhds (x := (4 * R + 12) * Real.pi)).add herr))
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n => (hU n).abs_finiteSupportDefect_le (hc n) hR (hbox n)) hrhs

theorem score_dyadic_tendsto {U : ℕ → Set Plane} {K : Set Plane} {a b : ℝ}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hab : a ≤ b)
    (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => score (U n) (dyadic (level n))) atTop
      (𝓝 (capScore K (Real.pi / 2))) := by
  have herror : Tendsto (fun n => score (U n) (dyadic (level n)) -
      capScore (U n) (Real.pi / 2)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlevel.eventually (eventually_score_error_le hab (half_pos hε)))
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn (U n) (hU n) (hbox n)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h.1]
    exact h.2.trans_lt (half_lt_self hε)
  have hscore := hHausdorff.capScore_pi_div_two_tendsto hU hK
    (isCompact_Icc.prod isCompact_Icc) hbox
  simpa only [sub_add_cancel, zero_add] using herror.add hscore

/-- The lengths are those of the actual selected polygon wings, including
their top segments. Their limit is the actual target score, not an assumed
perimeter or an ordinary niche-arclength limit. -/
theorem finiteWingLength_tendsto_twice_score_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteWingLength (U n) (normal (dyadic (level n)))) atTop
      (𝓝 (2 * capScore target (Real.pi / 2))) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hW : 1 < capWidth target := one_lt_M.trans_le hTarget.width_bounds.1
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hW
    linarith
  have hab : a ≤ b := by linarith
  have hscore := score_dyadic_tendsto hHausdorff hcap hTarget.isCap hab
    (fun n => (hU n).inBox) hlevel
  have hdefect := finiteSupportDefect_tendsto_zero_of_canonical_maximum hTarget hheight haffine
    hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have heR := selected_right_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hW hright
  have heL := selected_left_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hW hleft
  have hpR := rightPressure_tendsto hHausdorff hcap hTarget.isCap hlevel
    (fun n => (hU n).inBox) hpositive
  have hpL := leftPressure_tendsto hHausdorff hcap hTarget.isCap hlevel
    (fun n => (hU n).inBox) hpositive
  have hEP := hTarget.endpoint_heights_eq_pressures_of_affine hheight haffine
  have hlim := (((hscore.const_mul 2).add hdefect).sub (hr.mul (heR.sub hpR))).add
    (hl.mul (heL.sub hpL))
  have hgreen (n : ℕ) :
      2 * score (U n) (dyadic (level n)) +
        finiteSupportDefect (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none -
        horizontalRight (U n) * (capRoof (U n) (horizontalRight (U n)) -
          rightPressure (U n) (dyadic (level n))) +
        horizontalLeft (U n) * (capRoof (U n) (horizontalLeft (U n)) -
          leftPressure (U n) (dyadic (level n))) =
        finiteWingLength (U n) (normal (dyadic (level n))) := by
    have h := finiteSpatialScore_green (hcap n) (normal (dyadic (level n)))
      (normal_snd_pos (dyadic (level n))) (wallSlopes_injective (dyadic (level n)))
      (hU n).polygon_eq (pairList (dyadic (level n))) none
    change 2 * score (U n) (dyadic (level n)) =
      finiteWingLength (U n) (normal (dyadic (level n))) -
        finiteSupportDefect (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none +
        horizontalRight (U n) * (capRoof (U n) (horizontalRight (U n)) -
          rightPressure (U n) (dyadic (level n))) -
        horizontalLeft (U n) * (capRoof (U n) (horizontalLeft (U n)) -
          leftPressure (U n) (dyadic (level n))) at h
    linarith
  simpa only [hgreen, hEP.1, hEP.2, sub_self, mul_zero, add_zero, sub_zero] using hlim

end AngularGrid

end AmbidextrousSofa
