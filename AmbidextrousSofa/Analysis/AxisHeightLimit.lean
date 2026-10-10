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

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem exists_curvature_nonatom_Ioo (U : Set Plane) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, MovingSofaOptimality.sigmaAt U t = 0 := by
  have hdense := (MovingSofaOptimality.countable_sigma_singleton_ne U).dense_compl ℝ
  obtain ⟨t, ht, hnot⟩ := hdense.inter_open_nonempty (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hab)
  have hzero : MovingSofaOptimality.sigma U {t} = 0 := by
    simpa only [mem_compl_iff, mem_setOf_eq, not_not] using hnot
  exact ⟨t, ht, by simp only [MovingSofaOptimality.sigmaAt, hzero, ENNReal.toReal_zero]⟩

theorem subset_symmetricBox_of_horizontalBox {U : Set Plane} {a b : ℝ}
    (hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    U ⊆ Icc (-(|a| + |b| + 1)) (|a| + |b| + 1) ×ˢ Icc (0 : ℝ) 1 := by
  intro p hp
  have h := hbox hp
  refine ⟨⟨?_, ?_⟩, h.2⟩
  · linarith [neg_abs_le a, abs_nonneg b, h.1.1]
  · linarith [le_abs_self b, abs_nonneg a, h.1.2]

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
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have herr := selectionDefect_sum_tendsto (level := level) hTarget hcap hc hrate hHausdorff
  have hupper := MovingSofaOptimality.ang_le_sigmaAt_of_tendsto hcb hTarget.imported_isConvexBody hlim
    hheight (fun n => (hcap n).axis_curvature_zero.symm.le)
  change H ≤ (upperCurvature target {0}).toReal at hupper
  rw [hTarget.axis_curvature_zero] at hupper
  apply le_antisymm hupper
  by_contra hnot
  have hgap : 0 < capRoof target (horizontalRight target) - H :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let C : ℝ := 4 * R + 10
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hC1 : 0 < C + 1 := by linarith
  let δ := min (axisCutoff w) ((capRoof target (horizontalRight target) - H) / (C + 1))
  have hδ : 0 < δ := lt_min (axisCutoff_pos hw) (div_pos hgap hC1)
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target hδ
  have htcut : t ≤ axisCutoff w := ht.2.le.trans (min_le_left _ _)
  have htgap : t < (capRoof target (horizontalRight target) - H) / (C + 1) :=
    ht.2.trans_le (min_le_right _ _)
  have hbound : ∀ᶠ n in atTop,
      MovingSofaOptimality.sigmaFun (U n) t - capRoof (U n) (horizontalRight (U n)) ≤
        C * t + ∑ j, selectionDefect target (U n) (level n) (coefficient n) j := by
    filter_upwards [hW] with n hnW
    have h := (hU n).curvature_right_axis_bound (hc n) hR (hbox n) hw hnW ht.1.le htcut
    rwa [(hcap n).upperCurvature_real_Ioc_zero ht.1.le] at h
  have hleft : Tendsto
      (fun n => MovingSofaOptimality.sigmaFun (U n) t - capRoof (U n) (horizontalRight (U n))) atTop
        (𝓝 (MovingSofaOptimality.sigmaFun target t - H)) :=
    (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hfree).sub hheight
  have hright : Tendsto
      (fun n => C * t + ∑ j, selectionDefect target (U n) (level n) (coefficient n) j)
        atTop (𝓝 (C * t)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  have hle := le_of_tendsto_of_tendsto hleft hright hbound
  have hmono := MovingSofaOptimality.monotone_sigmaFun hTarget.imported_isConvexBody ht.1.le
  rw [hTarget.sigmaFun_zero] at hmono
  rw [lt_div_iff₀ hC1] at htgap
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
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have herr := selectionDefect_sum_tendsto (level := level) hTarget hcap hc hrate hHausdorff
  have hupper := MovingSofaOptimality.ang_le_sigmaAt_of_tendsto hcb hTarget.imported_isConvexBody hlim
    hheight (fun n => (hcap n).axis_curvature_pi.symm.le)
  change H ≤ (upperCurvature target {Real.pi}).toReal at hupper
  rw [hTarget.axis_curvature_pi] at hupper
  apply le_antisymm hupper
  by_contra hnot
  have hgap : 0 < capRoof target (horizontalLeft target) - H :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let C : ℝ := 4 * R + 10
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hC1 : 0 < C + 1 := by linarith
  let δ := min (axisCutoff w) ((capRoof target (horizontalLeft target) - H) / (C + 1))
  have hδ : 0 < δ := lt_min (axisCutoff_pos hw) (div_pos hgap hC1)
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target
    (by linarith : Real.pi - δ < Real.pi)
  let ε := Real.pi - t
  have hε : 0 < ε := by dsimp [ε]; linarith [ht.2]
  have hεδ : ε < δ := by dsimp [ε]; linarith [ht.1]
  have hεcut : ε ≤ axisCutoff w := hεδ.le.trans (min_le_left _ _)
  have hεgap : ε < (capRoof target (horizontalLeft target) - H) / (C + 1) :=
    hεδ.trans_le (min_le_right _ _)
  have hbound : ∀ᶠ n in atTop,
      (∫ s in (0 : ℝ)..Real.pi, MovingSofaOptimality.supp (U n) s) -
        capRoof (U n) (horizontalLeft (U n)) - MovingSofaOptimality.sigmaFun (U n) t ≤
          C * ε + ∑ j, selectionDefect target (U n) (level n) (coefficient n) j := by
    filter_upwards [hW] with n hnW
    have h := (hU n).curvature_left_axis_bound (hc n) hR (hbox n) hw hnW hε.le hεcut
    have hsub : Ioo t Real.pi ⊆ Ico (Real.pi - ε) Real.pi := by
      intro x hx
      refine ⟨?_, hx.2⟩
      dsimp only [ε]
      linarith [hx.1]
    have hmono : (upperCurvature (U n)).real (Ioo t Real.pi) ≤
        (upperCurvature (U n)).real (Ico (Real.pi - ε) Real.pi) :=
      measureReal_mono hsub measure_Ico_lt_top.ne
    have htotal := hmono.trans h
    rwa [(hcap n).upperCurvature_real_Ioo_pi ht.2] at htotal
  have hleft : Tendsto
      (fun n => (∫ s in (0 : ℝ)..Real.pi, MovingSofaOptimality.supp (U n) s) -
        capRoof (U n) (horizontalLeft (U n)) - MovingSofaOptimality.sigmaFun (U n) t) atTop
      (𝓝 ((∫ s in (0 : ℝ)..Real.pi, MovingSofaOptimality.supp target s) - H - MovingSofaOptimality.sigmaFun target t)) :=
    ((MovingSofaOptimality.ang_tendsto_integral_supp hcb hTarget.imported_isConvexBody hlim 0 Real.pi).sub
      hheight).sub (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hfree)
  have hright : Tendsto
      (fun n => C * ε + ∑ j, selectionDefect target (U n) (level n) (coefficient n) j)
        atTop (𝓝 (C * ε)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  have hle := le_of_tendsto_of_tendsto hleft hright hbound
  have hmono := (MovingSofaOptimality.monotone_sigmaFun hTarget.imported_isConvexBody).le_leftLim ht.2
  rw [hTarget.sigmaFun_leftLim_pi] at hmono
  rw [lt_div_iff₀ hC1] at hεgap
  nlinarith

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
      (Ioi_mem_nhds hwidth)).mono (fun _ hn => hn.le)
  have heq := selected_right_height_limit_eq hTarget hU hHausdorff hc hrate
    (by positivity : 0 ≤ |a| + |b| + 1)
    (fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox)
    (by norm_num : (0 : ℝ) < 1) hW hheight
  rwa [heq] at hheight

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
      (Ioi_mem_nhds hwidth)).mono (fun _ hn => hn.le)
  have heq := selected_left_height_limit_eq hTarget hU hHausdorff hc hrate
    (by positivity : 0 ≤ |a| + |b| + 1)
    (fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox)
    (by norm_num : (0 : ℝ) < 1) hW hheight
  rwa [heq] at hheight

end AngularGrid

end AmbidextrousSofa
