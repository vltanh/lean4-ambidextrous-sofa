module

public import AmbidextrousSofa.Analysis.PartialAxisCurvature
public import AmbidextrousSofa.Analysis.PartialPressureLimit
public import AmbidextrousSofa.Analysis.AxisHeightLimit

@[expose] public section

/-!
# Actual proper endpoint heights in the selected limit

The punctured-axis curvature estimates rule out a hidden limiting atom
next to either vertical face. Their rescaled mesh contribution tends to
zero. Hausdorff convergence at non-atomic interior angles consequently
identifies the independently constructed pressure limits with the actual
target endpoint heights.
-/

noncomputable section

open Set Filter MeasureTheory MovingSofaOptimality
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem selected_right_height_limit_eq {target : Set Plane} {U : ℕ → Set Plane}
    {a b R w H : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : ∀ᶠ n in atTop, w ≤ capWidth (U n))
    (hheight : Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop (𝓝 H)) :
    H = capRoof target (horizontalRight target) := by
  have hcap n := (hU n).isCap
  have hcb n := (hcap n).imported_isConvexBody
  have hK := hTarget.imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  refine le_antisymm ((ang_le_sigmaAt_of_tendsto hcb hK hlim hheight
    fun n => (hcap n).axis_curvature_zero.symm.le).trans_eq hTarget.axis_curvature_zero)
    (not_lt.1 fun hlt => ?_)
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target (lt_min (partialAxisCutoff_pos α hw)
    (div_pos (sub_pos.2 hlt) (by positivity : (0 : ℝ) < 8 * R + 24 + 1)))
  have hbound : ∀ᶠ n in atTop, sigmaFun (U n) t - capRoof (U n) (horizontalRight (U n)) ≤
      (8 * R + 24) * (t + mesh α (level n)) +
        ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j := by
    filter_upwards [hW] with n hnW
    rw [← (hcap n).upperCurvature_real_Ioc_zero ht.1.le]
    exact (hU n).curvature_right_axis_bound (hc n) hR (hbox n) hw hnW ht.1.le
      (ht.2.le.trans (min_le_left _ _))
  have hle := le_of_tendsto_of_tendsto ((ang_tendsto_sigmaFun hcb hK hlim hfree).sub hheight)
    (((((mesh_tendsto α).comp hlevel).const_add t).const_mul _).add
      (selectionDefect_sum_tendsto hTarget hcap hc hrate hHausdorff)) hbound
  have hmono := hTarget.sigmaFun_zero ▸ monotone_sigmaFun hK ht.1.le
  have hgap := ht.2.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hgap
  linarith [ht.1]

theorem selected_left_height_limit_eq {target : Set Plane} {U : ℕ → Set Plane}
    {a b R w H : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : ∀ᶠ n in atTop, w ≤ capWidth (U n))
    (hheight : Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop (𝓝 H)) :
    H = capRoof target (horizontalLeft target) := by
  have hcap n := (hU n).isCap
  have hcb n := (hcap n).imported_isConvexBody
  have hK := hTarget.imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  refine le_antisymm ((ang_le_sigmaAt_of_tendsto hcb hK hlim hheight
    fun n => (hcap n).axis_curvature_pi.symm.le).trans_eq hTarget.axis_curvature_pi)
    (not_lt.1 fun hlt => ?_)
  have hδ := lt_min (partialAxisCutoff_pos α hw)
    (div_pos (sub_pos.2 hlt) (by positivity : (0 : ℝ) < 8 * R + 24 + 1))
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target (sub_lt_self Real.pi hδ)
  have hε : Real.pi - t < min (partialAxisCutoff α w)
      ((capRoof target (horizontalLeft target) - H) / (8 * R + 24 + 1)) := by linarith [ht.1]
  have hbound : ∀ᶠ n in atTop, (∫ s in (0 : ℝ)..Real.pi, supp (U n) s) -
      capRoof (U n) (horizontalLeft (U n)) - sigmaFun (U n) t ≤
        (8 * R + 24) * (Real.pi - t + mesh α (level n)) +
          ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j := by
    filter_upwards [hW] with n hnW
    rw [← (hcap n).upperCurvature_real_Ioo_pi ht.2]
    refine (measureReal_mono ?_ measure_Ico_lt_top.ne).trans
      ((hU n).curvature_left_axis_bound (hc n) hR (hbox n) hw hnW (by linarith [ht.2])
        (hε.le.trans (min_le_left _ _)))
    exact fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hle := le_of_tendsto_of_tendsto
    (((ang_tendsto_integral_supp hcb hK hlim 0 Real.pi).sub hheight).sub
      (ang_tendsto_sigmaFun hcb hK hlim hfree))
    (((((mesh_tendsto α).comp hlevel).const_add _).const_mul _).add
      (selectionDefect_sum_tendsto hTarget hcap hc hrate hHausdorff)) hbound
  have hmono := hTarget.sigmaFun_leftLim_pi ▸ (monotone_sigmaFun hK).le_leftLim ht.2
  have hgap := hε.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hgap
  linarith [ht.2]

theorem selected_right_height_tendsto_actual {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target))) := by
  have hheight := selected_right_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
    hwidth hslack
  rwa [selected_right_height_limit_eq hTarget hU hHausdorff hlevel hc hrate (by positivity)
    (fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos
    (((hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
      (Ioi_mem_nhds hwidth)).mono fun _ hn => hn.le) hheight] at hheight

theorem selected_left_height_tendsto_actual {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target))) := by
  have hheight := selected_left_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
    hwidth hslack
  rwa [selected_left_height_limit_eq hTarget hU hHausdorff hlevel hc hrate (by positivity)
    (fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos
    (((hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
      (Ioi_mem_nhds hwidth)).mono fun _ hn => hn.le) hheight] at hheight

end PartialGrid
end AmbidextrousSofa
