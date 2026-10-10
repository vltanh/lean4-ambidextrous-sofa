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
    apply density_le_of_local_interval_bound hρ (fun t => (hρbounds t).1)
      (fun t => (hρbounds t).2) heq
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_sigmaAt_companionSourceAngle_eq_zero target)] with t ht hcomp
    intro ε hε
    have htwing : t ∈ Ioo A B := ⟨ha.trans ht.1, ht.2.trans hb⟩
    obtain ⟨δ, hδ, _, hlocal⟩ := curvature_local_source_bound hTarget hU hHausdorff hlevel
      hc hrate hR hbox hwidth haffine hA hB htop hterminal hperp htwing hcomp hε
    refine ⟨δ, hδ, ?_⟩
    intro d hd hdδ
    have h := hlocal t (t + d) (by linarith only [hδ])
      (by linarith only [hd]) (by linarith only [hdδ])
    simpa only [add_sub_cancel_left] using h
  let η := fun t => min (ρ t) (sourceKappa (upperCornerVelocity target t))
  have hη : Measurable η :=
    hρ.min (continuous_sourceKappa.measurable.comp hTarget.measurable_upperCornerVelocity)
  refine ⟨η, hη, ?_, ?_, heq.trans ?_⟩
  · intro t
    exact ⟨le_min (hρbounds t).1 (sourceKappa_nonneg _), min_le_right _ _⟩
  · intro t
    exact (min_le_left _ _).trans (hρbounds t).2
  · apply withDensity_congr_ae
    filter_upwards [hsharp] with t ht
    change ENNReal.ofReal (ρ t) = ENNReal.ofReal (min (ρ t) _)
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
  rw [heq]
  exact withDensity_mono (Eventually.of_forall (fun t => ENNReal.ofReal_le_ofReal (hρ t).2))

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
  let R := |horizontalLeft K| + |horizontalRight K| + 1
  let β : TerminalAngle := ⟨α, hK.angle_mem⟩
  have hR : 0 ≤ R := by positivity
  have hbox : K ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hK.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hK.isCap.nonempty hK.isCap.isCompact hK.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence β hproper hK (by linarith only [hR] : -R ≤ R) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hwidth : 0 < capWidth K := by linarith only [hK.width_bounds.1, one_lt_M]
  have hdom : (upperCurvature K).restrict (Ioo A B) ≤
      ((volume : Measure ℝ).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t)))).restrict (Ioo A B) := by
    apply measure_restrict_Ioo_le_of_compactly_contained
    intro a b ha hab hb
    have h := PartialGrid.curvature_restrict_le_source_density hK.isCap hU hHausdorff hlevelTop
      (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox) hwidth haffine
      hA hB htop hterminal hperp ha hab hb
    simpa only [restrict_withDensity measurableSet_Ioo] using h
  simpa only [restrict_withDensity measurableSet_Ioo] using hdom

end AmbidextrousSofa
