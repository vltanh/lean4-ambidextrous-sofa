module

public import AmbidextrousSofa.Analysis.PartialSharpSourceDensity
public import AmbidextrousSofa.Analysis.LeftCompanionDensity

@[expose] public section

/-!
# Actual sharp curvature densities for proper maxima

Lebesgue differentiation turns the proved local source interval bound
into the sharp bound on the actual curvature density. Open-wing
exhaustion and the literal selected sequence discharge every regularity
premise. The two companion wings are then joined away from the original
middle atom, and the proved left-cut splice removes that atom exactly.

All sharp coefficients below are evaluated at the original cap's
actual corner velocity. No occupation equality is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem curvature_density_sharp_on_wing
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
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity target t)) ∧
      (∀ t, ρ t ≤ 8 * R + 24) ∧
      (upperCurvature target).restrict (Ioo a b) =
        (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  obtain ⟨ρ, hρ, hρbounds, heq⟩ := curvature_density_on_wing hTarget hU hHausdorff hlevel
    hc hrate hR hbox hwidth haffine hA hB htop hterminal hperp ha hab hb
  have hsharp : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ρ t ≤ sourceKappa (upperCornerVelocity target t) := by
    refine density_le_of_local_interval_bound hρ (fun t => (hρbounds t).1)
      (fun t => (hρbounds t).2) heq ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_sigmaAt_companionSourceAngle_eq_zero target)] with t ht hcomp ε hε
    obtain ⟨δ, hδ, -, hlocal⟩ := curvature_local_source_bound hTarget hU hHausdorff hlevel hc
      hrate hR hbox hwidth haffine hA hB htop hterminal hperp ⟨ha.trans ht.1, ht.2.trans hb⟩
      hcomp hε
    refine ⟨δ, hδ, fun d hd hdδ => ?_⟩
    simpa only [add_sub_cancel_left] using
      hlocal t (t + d) (by linarith) (by linarith) (by linarith)
  refine ⟨fun t => min (ρ t) (sourceKappa (upperCornerVelocity target t)),
    hρ.min (continuous_sourceKappa.measurable.comp hTarget.measurable_upperCornerVelocity),
    fun t => ⟨le_min (hρbounds t).1 (sourceKappa_nonneg _), min_le_right _ _⟩,
    fun t => (min_le_left _ _).trans (hρbounds t).2, heq.trans (withDensity_congr_ae ?_)⟩
  filter_upwards [hsharp] with t ht
  rw [min_eq_left ht]

theorem curvature_restrict_le_source_density
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
    (upperCurvature target).restrict (Ioo a b) ≤
      (volume.restrict (Ioo a b)).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity target t))) := by
  obtain ⟨ρ, _, hρ, _, heq⟩ := curvature_density_sharp_on_wing hTarget hU hHausdorff hlevel
    hc hrate hR hbox hwidth haffine hA hB htop hterminal hperp ha hab hb
  exact heq ▸ withDensity_mono (.of_forall fun t => ENNReal.ofReal_le_ofReal (hρ t).2)

end PartialGrid

/-- The selected sequence belongs to this actual joint maximum and is
constructed here. The terminal normal stays outside the open wing. -/
theorem IsJointCapMaximizer.curvature_restrict_le_source_density_on_proper_open_wing
    {K : Set Plane} {α m c A B : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : α ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) :
    (upperCurvature K).restrict (Ioo A B) ≤
      (volume.restrict (Ioo A B)).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t))) := by
  have hR : 0 ≤ |horizontalLeft K| + |horizontalRight K| + 1 := by positivity
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hK.angle_mem⟩ hproper hK (neg_le_self hR)
      (subset_symmetricBox_of_horizontalBox fun p hp =>
        ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  rw [← restrict_withDensity measurableSet_Ioo]
  refine measure_restrict_Ioo_le_of_compactly_contained fun a b ha hab hb => ?_
  rw [restrict_withDensity measurableSet_Ioo]
  exact PartialGrid.curvature_restrict_le_source_density hK.isCap hU hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox)
    (by linarith only [hK.width_bounds.1, one_lt_M]) haffine hA hB htop hterminal hperp ha hab hb

end AmbidextrousSofa
