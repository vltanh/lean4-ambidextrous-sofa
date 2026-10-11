module

public import AmbidextrousSofa.Analysis.DyadicCurvatureMass
public import AmbidextrousSofa.Analysis.AxisFaces
public import AmbidextrousSofa.Analysis.SelectedPressureLimit
public import MovingSofaOptimality.Angle.HorizontalSide
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-!
# Axis heights in the actual selected limit

Curvature bounds on punctured neighborhoods of the axes prevent curvature
from concentrating next to an axis. At every non-atomic interior angle the
actual Stieltjes distribution converges under Hausdorff convergence. These
facts identify any limit of face heights with the actual target face height.
For the selected polygons the finite-pressure limit supplies such a limit,
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

section

variable {target : Set Plane} {U : ℕ → Set Plane} {C δ H : ℝ} {E : ℕ → ℝ}
  (hHausdorff : CapHausdorffTendsto U target) (hU : ∀ n, IsDownwardCap (U n))
  (hTarget : IsDownwardCap target) (hδ : 0 < δ) (hE : Tendsto E atTop (𝓝 0))
include hHausdorff hU hTarget hδ hE

/-- Curvature on `(0, ε]` at most `C * ε` up to errors tending to zero identifies the limit of
the right face heights with the target's right face height. -/
theorem CapHausdorffTendsto.right_height_eq_of_axis_bound
    (hbound : ∀ ε, 0 ≤ ε → ε ≤ δ →
      ∀ᶠ n in atTop, (upperCurvature (U n)).real (Ioc 0 ε) ≤ C * ε + E n)
    (hheight : Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop (𝓝 H)) :
    H = capRoof target (horizontalRight target) := by
  have hcb n := (hU n).imported_isConvexBody
  have hK := hTarget.imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hU hTarget
  refine le_antisymm ((ang_le_sigmaAt_of_tendsto hcb hK hlim hheight
    fun n => (hU n).axis_curvature_zero.symm.le).trans_eq hTarget.axis_curvature_zero)
    (not_lt.1 fun hlt => ?_)
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target
    (lt_min hδ (div_pos (sub_pos.2 hlt) (by positivity : (0 : ℝ) < |C| + 1)))
  have hle := le_of_tendsto_of_tendsto ((ang_tendsto_sigmaFun hcb hK hlim hfree).sub hheight)
    (tendsto_const_nhds.add hE) ((hbound t ht.1.le (ht.2.le.trans (min_le_left _ _))).mono
      fun n hn => (hU n).upperCurvature_real_Ioc_zero ht.1.le ▸ hn)
  have hmono := hTarget.sigmaFun_zero ▸ monotone_sigmaFun hK ht.1.le
  have hgap := ht.2.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hgap
  linarith [ht.1, mul_le_mul_of_nonneg_right (le_abs_self C) ht.1.le]

/-- Curvature on `[π - ε, π)` at most `C * ε` up to errors tending to zero identifies the limit
of the left face heights with the target's left face height. -/
theorem CapHausdorffTendsto.left_height_eq_of_axis_bound
    (hbound : ∀ ε, 0 ≤ ε → ε ≤ δ →
      ∀ᶠ n in atTop, (upperCurvature (U n)).real (Ico (Real.pi - ε) Real.pi) ≤ C * ε + E n)
    (hheight : Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop (𝓝 H)) :
    H = capRoof target (horizontalLeft target) := by
  have hcb n := (hU n).imported_isConvexBody
  have hK := hTarget.imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hU hTarget
  refine le_antisymm ((ang_le_sigmaAt_of_tendsto hcb hK hlim hheight
    fun n => (hU n).axis_curvature_pi.symm.le).trans_eq hTarget.axis_curvature_pi)
    (not_lt.1 fun hlt => ?_)
  have hδ' := lt_min hδ (div_pos (sub_pos.2 hlt) (by positivity : (0 : ℝ) < |C| + 1))
  obtain ⟨t, ht, hfree⟩ := exists_curvature_nonatom_Ioo target (sub_lt_self Real.pi hδ')
  have hε : Real.pi - t < min δ ((capRoof target (horizontalLeft target) - H) / (|C| + 1)) := by
    linarith [ht.1]
  have hle := le_of_tendsto_of_tendsto
    (((ang_tendsto_integral_supp hcb hK hlim 0 Real.pi).sub hheight).sub
      (ang_tendsto_sigmaFun hcb hK hlim hfree))
    ((tendsto_const_nhds (x := C * (Real.pi - t))).add hE)
    ((hbound _ (by linarith [ht.2]) (hε.le.trans (min_le_left _ _))).mono fun n hn => by
      dsimp only
      rw [← (hU n).upperCurvature_real_Ioo_pi ht.2]
      refine (measureReal_mono ?_ measure_Ico_lt_top.ne).trans hn
      exact fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hmono := hTarget.sigmaFun_leftLim_pi ▸ (monotone_sigmaFun hK).le_leftLim ht.2
  have hgap := hε.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hgap
  linarith [ht.2, mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.2 ht.2.le)]

end

namespace AngularGrid

variable {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
  {coefficient : ℕ → ℝ}

theorem selected_right_height_tendsto_actual
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target))) := by
  have hS := selectedLimit hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
  have hheight := hS.right_height_tendsto hslack
  rwa [hHausdorff.right_height_eq_of_axis_bound hS.isCap hTarget (axisCutoff_pos one_pos)
    (selectionDefect_sum_tendsto hTarget hS.isCap hc hrate hHausdorff)
    (fun ε hε hεδ => hS.eventually_one_le_capWidth.mono fun n hW =>
      (hU n).curvature_right_axis_bound (hc n) (by positivity)
        (subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos hW hε hεδ) hheight] at hheight

theorem selected_left_height_tendsto_actual
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target))) := by
  have hS := selectedLimit hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
  have hheight := hS.left_height_tendsto hslack
  rwa [hHausdorff.left_height_eq_of_axis_bound hS.isCap hTarget (axisCutoff_pos one_pos)
    (selectionDefect_sum_tendsto hTarget hS.isCap hc hrate hHausdorff)
    (fun ε hε hεδ => hS.eventually_one_le_capWidth.mono fun n hW =>
      (hU n).curvature_left_axis_bound (hc n) (by positivity)
        (subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos hW hε hεδ) hheight] at hheight

end AngularGrid

end AmbidextrousSofa
