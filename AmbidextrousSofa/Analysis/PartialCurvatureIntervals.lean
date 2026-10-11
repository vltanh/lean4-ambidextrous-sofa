module

public import AmbidextrousSofa.Analysis.PartialSourceCounting
public import AmbidextrousSofa.Analysis.MiddleMassLimit
public import AmbidextrousSofa.Analysis.AxisHeightLimit

@[expose] public section

/-!
# Actual proper-angle curvature bounds on regular intervals

The selected polygon source bound passes to every compact angular
interval separated from the top, middle-facet and terminal normals.
Non-atomic endpoints are first used for weak Stieltjes convergence and
then removed by outward approximation through non-atoms.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem curvature_Ioc_le_of_nonatoms
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ Icc a b) (hterminal : (α : ℝ) ∉ Icc a b)
    (hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0)
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0) :
    (upperCurvature target).real (Ioc a b) ≤ (8 * R + 24) * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb (n : ℕ) := (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  refine le_of_tendsto_of_tendsto' (b := atTop) ?_ ?_
    fun n => (hU n).curvature_Ioc_le (hc n) hR (hbox n) hab hupper htop hterminal
  · simpa only [(hcap _).upperCurvature_real_Ioc hab, hTarget.upperCurvature_real_Ioc hab] using
      (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb).sub
        (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha)
  · simpa only [add_zero, Function.comp_apply] using
      ((((tendsto_const_nhds.add ((mesh_tendsto α).comp hlevel)).const_mul (8 * R + 24)).add
        ((AngularGrid.middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
          (grid := fun n => outerGrid α (dyadic (level n))) (fun n => (hU n).polygon_eq) hbox
          hwidth haffine isCompact_Icc hupper hperp).congr fun n => by
            rw [Finset.filter_congr_decidable]; rfl)).add
        (selectionDefect_sum_tendsto (α := α) (level := level) hTarget hcap hc hrate hHausdorff))

/-- Every closed subinterval of a wing obeys the linear curvature bound.
Its endpoints need not be non-atoms. The singleton case is included. -/
theorem curvature_Icc_le_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : (α : ℝ) ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    (upperCurvature target).real (Icc a b) ≤ (8 * R + 24) * (b - a) := by
  have hC : 0 ≤ 8 * R + 24 := by linarith
  refine ge_of_tendsto (x := 𝓝[>] 0) (f := fun δ => (8 * R + 24) * (b - a + 2 * δ))
    (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) _ _ (by simp))) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))] with δ ⟨hδ0, hδ⟩
  obtain ⟨a', ha', hfreea⟩ := exists_curvature_nonatom_Ioo target (sub_lt_self a hδ0)
  obtain ⟨b', hb', hfreeb⟩ := exists_curvature_nonatom_Ioo target (lt_add_of_pos_right b hδ0)
  have hsub : Icc a' b' ⊆ Ioo A B := fun t ht =>
    ⟨by linarith [ht.1, ha'.1, hδ.trans_le (min_le_left _ _)],
      by linarith [ht.2, hb'.2, hδ.trans_le (min_le_right _ _)]⟩
  refine (measureReal_mono (Icc_subset_Ioc ha'.2 hb'.1.le) measure_Ioc_lt_top.ne).trans
    ((curvature_Ioc_le_of_nonatoms hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth haffine
      (by linarith [ha'.2, hb'.1]) (hsub.trans (Ioo_subset_Ioo hA hB)) (fun ht => htop (hsub ht))
      (fun ht => hterminal (hsub ht)) (fun t ht => hperp t (hsub ht)) hfreea hfreeb).trans
      (mul_le_mul_of_nonneg_left (by linarith [ha'.1, hb'.2]) hC))

theorem curvature_singleton_eq_zero_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B t : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : (α : ℝ) ∉ Ioo A B)
    (hperp : ∀ s ∈ Ioo A B, Real.cos s + m * Real.sin s ≠ 0)
    (ht : t ∈ Ioo A B) : upperCurvature target {t} = 0 := by
  have h := curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox
    hwidth haffine hA hB htop hterminal hperp ht.1 le_rfl ht.2
  rw [Icc_self, sub_self, mul_zero] at h
  exact (measureReal_eq_zero_iff isCompact_singleton.measure_ne_top).mp
    (h.antisymm measureReal_nonneg)

end PartialGrid

end AmbidextrousSofa
