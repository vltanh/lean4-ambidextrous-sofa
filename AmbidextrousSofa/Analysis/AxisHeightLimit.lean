module

public import AmbidextrousSofa.Analysis.DyadicCurvatureMass
public import AmbidextrousSofa.Analysis.AxisFaces
public import AmbidextrousSofa.Analysis.SelectedPressureLimit
public import MovingSofaOptimality.Angle.HorizontalSide
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-!
# Axis heights in the actual selected limit

The punctured-axis bounds prevent curvature from concentrating next to
an axis. At every non-atomic interior angle the actual Stieltjes
distribution converges under Hausdorff convergence. These facts identify
any limit of selected face heights with the actual target face height.
The independently proved finite-pressure limit supplies such a limit,
including zero-height endpoint faces.
-/

open Set Filter MeasureTheory MovingSofaOptimality
open scoped Topology

namespace AmbidextrousSofa

theorem exists_curvature_nonatom_Ioo (U : Set Plane) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, MovingSofaOptimality.sigmaAt U t = 0 := by
  obtain ⟨t, ht, hnot⟩ := ((countable_sigma_singleton_ne U).dense_compl ℝ).inter_open_nonempty
    (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hab)
  exact ⟨t, ht, by rw [sigmaAt, not_not.1 hnot, ENNReal.toReal_zero]⟩

theorem subset_symmetricBox_of_horizontalBox {U : Set Plane} {a b : ℝ}
    (hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    U ⊆ Icc (-(|a| + |b| + 1)) (|a| + |b| + 1) ×ˢ Icc (0 : ℝ) 1 := fun _ hp =>
  have h := hbox hp
  ⟨⟨by linarith [neg_abs_le a, abs_nonneg b, h.1.1],
    by linarith [le_abs_self b, abs_nonneg a, h.1.2]⟩, h.2⟩

namespace AngularGrid

theorem selected_right_height_limit_eq {target : Set Plane} {U : ℕ → Set Plane}
    {a b R w H : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : ∀ᶠ n in atTop, w ≤ capWidth (U n))
    (hheight : Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop (𝓝 H)) :
    H = capRoof target (horizontalRight target) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hK := hTarget.imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hupper := ang_le_sigmaAt_of_tendsto hcb hK hlim hheight
    fun n => (hcap n).axis_curvature_zero.symm.le
  change H ≤ (upperCurvature target {0}).toReal at hupper
  rw [hTarget.axis_curvature_zero] at hupper
  refine le_antisymm hupper (not_lt.1 fun hlt => ?_)
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target (lt_min (axisCutoff_pos hw)
    (div_pos (sub_pos.2 hlt) (by positivity : (0 : ℝ) < 4 * R + 10 + 1)))
  have hbound : ∀ᶠ n in atTop, sigmaFun (U n) t - capRoof (U n) (horizontalRight (U n)) ≤
      (4 * R + 10) * t + ∑ j, selectionDefect target (U n) (level n) (coefficient n) j := by
    filter_upwards [hW] with n hnW
    rw [← (hcap n).upperCurvature_real_Ioc_zero ht.1.le]
    exact (hU n).curvature_right_axis_bound (hc n) hR (hbox n) hw hnW ht.1.le
      (ht.2.le.trans (min_le_left _ _))
  have hle := le_of_tendsto_of_tendsto ((ang_tendsto_sigmaFun hcb hK hlim hfree).sub hheight)
    (tendsto_const_nhds.add (selectionDefect_sum_tendsto hTarget hcap hc hrate hHausdorff)) hbound
  have hmono := hTarget.sigmaFun_zero ▸ monotone_sigmaFun hK ht.1.le
  have hgap := ht.2.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hgap
  nlinarith [ht.1]

theorem selected_left_height_limit_eq {target : Set Plane} {U : ℕ → Set Plane}
    {a b R w H : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : ∀ᶠ n in atTop, w ≤ capWidth (U n))
    (hheight : Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop (𝓝 H)) :
    H = capRoof target (horizontalLeft target) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hK := hTarget.imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hupper := ang_le_sigmaAt_of_tendsto hcb hK hlim hheight
    fun n => (hcap n).axis_curvature_pi.symm.le
  change H ≤ (upperCurvature target {Real.pi}).toReal at hupper
  rw [hTarget.axis_curvature_pi] at hupper
  refine le_antisymm hupper (not_lt.1 fun hlt => ?_)
  have hδ := lt_min (axisCutoff_pos hw)
    (div_pos (sub_pos.2 hlt) (by positivity : (0 : ℝ) < 4 * R + 10 + 1))
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target (sub_lt_self Real.pi hδ)
  have hε : Real.pi - t < min (axisCutoff w)
      ((capRoof target (horizontalLeft target) - H) / (4 * R + 10 + 1)) := by linarith [ht.1]
  have hbound : ∀ᶠ n in atTop, (∫ s in (0 : ℝ)..Real.pi, supp (U n) s) -
      capRoof (U n) (horizontalLeft (U n)) - sigmaFun (U n) t ≤ (4 * R + 10) * (Real.pi - t) +
        ∑ j, selectionDefect target (U n) (level n) (coefficient n) j := by
    filter_upwards [hW] with n hnW
    rw [← (hcap n).upperCurvature_real_Ioo_pi ht.2]
    refine (measureReal_mono ?_ measure_Ico_lt_top.ne).trans
      ((hU n).curvature_left_axis_bound (hc n) hR (hbox n) hw hnW (by linarith [ht.2])
        (hε.le.trans (min_le_left _ _)))
    exact fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hle := le_of_tendsto_of_tendsto
    (((ang_tendsto_integral_supp hcb hK hlim 0 Real.pi).sub hheight).sub
      (ang_tendsto_sigmaFun hcb hK hlim hfree))
    (tendsto_const_nhds.add (selectionDefect_sum_tendsto hTarget hcap hc hrate hHausdorff)) hbound
  have hmono := hTarget.sigmaFun_leftLim_pi ▸ (monotone_sigmaFun hK).le_leftLim ht.2
  have hgap := hε.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hgap
  nlinarith [ht.2]

theorem selected_right_height_tendsto_actual {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target))) := by
  have hheight := selected_right_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
    hwidth hslack
  have hW : ∀ᶠ n in atTop, 1 ≤ capWidth (U n) :=
    ((hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
      (Ioi_mem_nhds hwidth)).mono fun _ hn => hn.le
  rwa [selected_right_height_limit_eq hTarget hU hHausdorff hc hrate (by positivity)
    (fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos hW hheight] at hheight

theorem selected_left_height_tendsto_actual {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target))) := by
  have hheight := selected_left_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
    hwidth hslack
  have hW : ∀ᶠ n in atTop, 1 ≤ capWidth (U n) :=
    ((hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
      (Ioi_mem_nhds hwidth)).mono fun _ hn => hn.le
  rwa [selected_left_height_limit_eq hTarget hU hHausdorff hc hrate (by positivity)
    (fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos hW hheight] at hheight

end AngularGrid

end AmbidextrousSofa
