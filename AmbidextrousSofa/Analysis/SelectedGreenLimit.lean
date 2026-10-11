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
  calc
    _ ≤ ∑ j, |normalizedExposureDefect U (dyadic level) j| *
          ((R + 1) * |(normal (dyadic level) j).1| + (1 - capHeight U)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hU.isCap.abs_support_sub_one_le_box hbox
          (normal_unit _ j) (normal_snd_pos _ j).le) (abs_nonneg _))
    _ = (R + 1) * ∑ j, |(normal (dyadic level) j).1| *
          |normalizedExposureDefect U (dyadic level) j| +
        (1 - capHeight U) * ∑ j, |normalizedExposureDefect U (dyadic level) j| := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (hU.sum_cos_abs_normalizedExposureDefect_le hc) (by linarith))
      (mul_le_mul_of_nonneg_left (hU.sum_abs_normalizedExposureDefect_le hc hR hbox)
        (sub_nonneg.2 hU.isCap.capHeight_le_one))

theorem score_dyadic_tendsto {U : ℕ → Set Plane} {K : Set Plane} {a b : ℝ}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hab : a ≤ b)
    (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => score (U n) (dyadic (level n))) atTop
      (𝓝 (capScore K (Real.pi / 2))) := by
  have herror : Tendsto (fun n => score (U n) (dyadic (level n)) -
      capScore (U n) (Real.pi / 2)) atTop (𝓝 0) :=
    Metric.tendsto_nhds.2 fun ε hε => (hlevel.eventually (eventually_score_error_le hab
      (half_pos hε))).mono fun n hn => by
        have h := hn (U n) (hU n) (hbox n)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg h.1]
        exact h.2.trans_lt (half_lt_self hε)
  simpa only [sub_add_cancel, zero_add] using herror.add
    (hHausdorff.capScore_pi_div_two_tendsto hU hK (isCompact_Icc.prod isCompact_Icc) hbox)

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
  -- The weighted source defect tends to zero.
  have hdefect : Tendsto (fun n => finiteSupportDefect (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) := by
    have herr := selectionDefect_sum_tendsto (level := level) hTarget.isCap hcap hc hrate hHausdorff
    have hH := hheight ▸ hHausdorff.capHeight_tendsto hcap hTarget.isCap
    have hD := erosionMoments_tendsto_zero_of_canonical_maximum hTarget hheight haffine
      hTargetBox hU hHausdorff hlevel hc hrate hleft hright
    refine squeeze_zero_norm (fun n => (hU n).abs_finiteSupportDefect_le (hc n) (by positivity)
      (subset_symmetricBox_of_horizontalBox (hU n).inBox)) ?_
    simpa using (((hD.1.add hD.2).add (herr.const_mul 2)).const_mul (|a| + |b| + 1 + 1)).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hH).mul
        ((tendsto_const_nhds (x := (4 * (|a| + |b| + 1) + 12) * Real.pi)).add herr))
  have hW : 1 < capWidth target := one_lt_M.trans_le hTarget.width_bounds.1
  have hpos : horizontalLeft target < horizontalRight target := sub_pos.1 (zero_lt_one.trans hW)
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hR := (selected_right_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hW hright).sub (rightPressure_tendsto hHausdorff hcap hTarget.isCap hlevel
      (fun n => (hU n).inBox) hpos)
  have hL := (selected_left_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hW hleft).sub (leftPressure_tendsto hHausdorff hcap hTarget.isCap hlevel
      (fun n => (hU n).inBox) hpos)
  have hEP := hTarget.endpoint_heights_eq_pressures_of_affine hheight haffine
  -- The exact finite Green identity, term by term.
  convert ((((score_dyadic_tendsto hHausdorff hcap hTarget.isCap (by linarith)
    (fun n => (hU n).inBox) hlevel).const_mul 2).add hdefect).sub (hr.mul hR)).add (hl.mul hL)
    using 2 with n
  · simp only [score, rightPressure, leftPressure]
    linarith [finiteSpatialScore_green (hcap n) _ (normal_snd_pos (dyadic (level n)))
      (wallSlopes_injective _) (hU n).polygon_eq (pairList (dyadic (level n))) none]
  · rw [hEP.1, hEP.2]
    ring

end AngularGrid

end AmbidextrousSofa
