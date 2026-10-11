module

public import AmbidextrousSofa.Analysis.NonpositiveCornerCurvature

@[expose] public section

/-!
# From actual selected atoms to local density inequalities

Summing an eventual finite atom bound retains the actual middle-face and
support-selection errors. Their proved vanishing limits then give an
interval bound for the actual target curvature. A conditional local bound
is transferred to any bounded density of that measure by the global
Lebesgue differentiation theorem, in the form used for the sharp
densities.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem sigmaAt_eq_zero_of_density {U : Set Plane} {S : Set ℝ} {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    {t : ℝ} (ht : t ∈ S) : MovingSofaOptimality.sigmaAt U t = 0 := by
  change (upperCurvature U).real {t} = 0
  rw [measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq (measurableSet_singleton t)
    (singleton_subset_iff.mpr ht)]
  simp

theorem ae_density_le_of_conditional_local_bound
    {μ : Measure ℝ} {ρ f : ℝ → ℝ} {S : Set ℝ} {P : ℝ → Prop} {C : ℝ}
    (hS : IsOpen S) (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hlocal : ∀ t ∈ S, P t → ∀ ε > 0,
      ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ → μ.real (Ioc t (t + d)) ≤ (f t + ε) * d) :
    ∀ᵐ t : ℝ ∂volume, t ∈ S → P t → ρ t ≤ f t :=
  ae_density_le_of_local_bound hS hρ hρ0 hρC heq hlocal

namespace AngularGrid

theorem curvature_Ioc_le_of_eventual_atom_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c C a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hC : 0 ≤ C) (hab : a ≤ b) (hregular : Icc a b ⊆ regularCurvatureDomain m)
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0)
    (hatom : ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      fullAngle (dyadic (level n)) j ∈ Icc a b →
        (upperCurvature (U n) {fullAngle (dyadic (level n)) j}).toReal ≤
          C * mesh (level n) + middleOuterMass (U n) (dyadic (level n)) j +
            selectionDefect target (U n) (level n) (coefficient n) j) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
  have hupper := hregular.trans (regularCurvatureDomain_subset m)
  have hreg {t} (ht : t ∈ Icc a b) := mem_regularCurvatureDomain_iff.mp (hregular ht)
  exact curvature_Ioc_le_of_eventually_le hTarget (fun n => (hU n).isCap)
    (fun n => (hU n).polygon_eq) hHausdorff hbox hwidth haffine hab hupper
    (fun t ht => (hreg ht).2.2.2) ha hb (mesh_tendsto.comp hlevel)
    (selectionDefect_sum_tendsto hTarget (fun n => (hU n).isCap) hc hrate hHausdorff)
    (hatom.mono fun n hn => upperCurvature_real_le_of_atom_bound (hU n).isCap _ (hU n).polygon_eq
      (Ioc_subset_Icc_self.trans hupper) (fun ht => (hreg (Ioc_subset_Icc_self ht)).2.2.1 rfl)
      (fun _ hj => Ioc_subset_Icc_self hj) hC (fun _ => (mesh_pos _).le)
      (middleOuterMass_nonneg (hU n).isCap _) (selectionDefect_nonneg target (U n) _ (hc n)) hn
      (sum_mesh_interval_sources_le _ hab))

end AngularGrid

end AmbidextrousSofa
