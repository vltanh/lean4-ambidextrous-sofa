module

public import AmbidextrousSofa.Analysis.PartialSourceCounting
public import AmbidextrousSofa.Analysis.WingCurvatureIntervals

@[expose] public section

/-!
# Actual proper-angle curvature bounds on regular intervals

The selected polygon source bound passes to every compact angular
interval separated from the top, middle-facet and terminal normals.
Non-atomic endpoints are first used for weak Stieltjes convergence and
then removed by outward approximation through non-atoms; both steps are
the general ones proved for the full-turn wings. The selected sequence
of a proper joint maximizer is fixed here in a symmetric box.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

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
    (upperCurvature target).real (Icc a b) ≤ (8 * R + 24) * (b - a) :=
  upperCurvature_real_Icc_le_of_nonatoms (by linarith) (fun a' b' hab' hsub ha' hb' =>
    have hupper := hsub.trans (Ioo_subset_Ioo hA hB)
    curvature_Ioc_le_of_eventually_le hTarget (fun n => (hU n).isCap) (fun n => (hU n).polygon_eq)
      hHausdorff hbox hwidth haffine hab' hupper (fun t ht => hperp t (hsub ht)) ha' hb'
      ((mesh_tendsto α).comp hlevel)
      (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap) hc hrate hHausdorff)
      (.of_forall fun n => (hU n).curvature_Ioc_le (hc n) hR (hbox n) hab' hupper
        (fun ht => htop (hsub ht)) fun ht => hterminal (hsub ht))) ha hab hb

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

/-- A proper joint maximizer is the Hausdorff limit of selected polygons in the symmetric box
of half-width `|horizontalLeft K| + |horizontalRight K| + 1`, with levels tending to infinity. -/
theorem IsJointCapMaximizer.exists_symmetric_selected_sequence {K : Set Plane} {α : ℝ}
    (hK : IsJointCapMaximizer K α) (hproper : α < Real.pi / 2) :
    ∃ (level : ℕ → ℕ) (coefficient : ℕ → ℝ) (U : ℕ → Set Plane), Tendsto level atTop atTop ∧
      (∀ n, 0 ≤ coefficient n) ∧ Tendsto coefficient atTop (𝓝 0) ∧
      (∀ n, PartialGrid.IsSelectedPolygon K ⟨α, hK.angle_mem⟩ hproper
        (-(|horizontalLeft K| + |horizontalRight K| + 1))
        (|horizontalLeft K| + |horizontalRight K| + 1) (level n) (coefficient n) (U n)) ∧
      CapHausdorffTendsto U K := by
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hK.angle_mem⟩ hproper hK (neg_le_self (by positivity))
      (subset_symmetricBox_of_horizontalBox fun p hp =>
        ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  exact ⟨level, coefficient, U, tendsto_atTop_mono hlevel tendsto_id, fun n => (hc n).le, hrate,
    hU, hHausdorff⟩

end AmbidextrousSofa
