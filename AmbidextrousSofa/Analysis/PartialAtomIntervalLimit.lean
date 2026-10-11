module

public import AmbidextrousSofa.Analysis.PartialRegularDomain

@[expose] public section

/-!
# Summing actual proper sampled atom bounds

A compact interval away from the top meets at most one rescaled source
family. Every unsampled nonterminal atom is still counted and has only
the middle-facet and selection errors. This converts a local bound on
the actual sampled atoms into a bound on the limiting curvature measure.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

open Classical in
theorem IsSelectedPolygon.curvature_Ioc_le_of_sampled_atom_bound
    {target U : Set Plane} {boxLeft boxRight coefficient C a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hC : 0 ≤ C) (hab : a ≤ b)
    (hupper : Icc a b ⊆ Ioo (0 : ℝ) Real.pi) (htop : Real.pi / 2 ∉ Icc a b)
    (hterminal : (α : ℝ) ∉ Icc a b)
    (hsampled : ∀ k : AngularGrid.SourceIndex (dyadic level),
      fullAngle α (dyadic level) (scaledSource α (dyadic level) k) ∈ Icc a b →
        (upperCurvature U {fullAngle α (dyadic level) (scaledSource α (dyadic level) k)}).toReal ≤
          C * mesh α level + middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) k) +
            selectionDefect target U α level coefficient (scaledSource α (dyadic level) k)) :
    (upperCurvature U).real (Ioc a b) ≤ C * (b - a + mesh α level) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
        fullAngle α (dyadic level) j ∈ Icc a b), middleOuterMass U α (dyadic level) j) +
      ∑ j, selectionDefect target U α level coefficient j := by
  -- spread each sampled atom bound `C * mesh` over the scaled sources
  have hw (q : AngularGrid.SourceIndex (dyadic level)) (j : SourceIndex α (dyadic level)) :
      0 ≤ if scaledSource α (dyadic level) q = j then mesh α level else 0 :=
    ite_nonneg (mesh_pos α level).le le_rfl
  refine upperCurvature_real_le_of_atom_bound hU.isCap (outerGrid α (dyadic level)) hU.polygon_eq
    (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))
    (q := fun j => fullAngle α (dyadic level) j ∈ Icc a b)
    (δ := fun j => ∑ k, if scaledSource α (dyadic level) k = j then mesh α level else 0)
    (fun _ hj => Ioc_subset_Icc_self hj) hC (fun j => Finset.sum_nonneg fun k _ => hw k j)
    (middleOuterMass_nonneg hU.isCap α _) (selectionDefect_nonneg target U α level hc)
    (fun j hj => ?_) ?_
  · change (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤ _
    by_cases hscaled : ∃ k, j = scaledSource α (dyadic level) k
    · obtain ⟨k, rfl⟩ := hscaled
      have := Finset.single_le_sum (fun q _ => hw q (scaledSource α (dyadic level) k))
        (Finset.mem_univ k)
      rw [ite_eq_left rfl] at this
      linarith [hsampled k hj, mul_le_mul_of_nonneg_left this hC]
    · have h := hU.curvature_atom_le_mass hc j
      rw [innerSourceMass_eq_zero_of_not_scaled U α hαL _ j (by rintro rfl; exact hterminal hj)
        hscaled] at h
      linarith [mul_nonneg hC (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hw k j)]
  · rw [Finset.sum_comm]
    simpa only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and] using
      sum_mesh_scaled_sources_interval_le_of_no_top α level hab htop

theorem curvature_Ioc_le_of_eventual_sampled_atom_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c C a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hC : 0 ≤ C) (hab : a ≤ b) (hregular : Icc a b ⊆ regularProperCurvatureDomain α m)
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0)
    (hsampled : ∀ᶠ n in atTop, ∀ k : AngularGrid.SourceIndex (dyadic (level n)),
      fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) k) ∈ Icc a b →
        (upperCurvature (U n)
          {fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) k)}).toReal ≤
          C * mesh α (level n) +
            middleOuterMass (U n) α (dyadic (level n)) (scaledSource α (dyadic (level n)) k) +
              selectionDefect target (U n) α (level n) (coefficient n)
                (scaledSource α (dyadic (level n)) k)) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
  have hupper := hregular.trans (regularProperCurvatureDomain_subset α m)
  have hreg {t} (ht : t ∈ Icc a b) := mem_regularCurvatureDomain_iff.mp (hregular ht).1
  exact curvature_Ioc_le_of_eventually_le hTarget (fun n => (hU n).isCap)
    (fun n => (hU n).polygon_eq) hHausdorff hbox hwidth haffine hab hupper
    (fun t ht => (hreg ht).2.2.2) ha hb ((mesh_tendsto α).comp hlevel)
    (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap) hc hrate hHausdorff)
    (hsampled.mono fun n hn => (hU n).curvature_Ioc_le_of_sampled_atom_bound (hc n) hC hab hupper
      (fun h => (hreg h).2.2.1 rfl) (fun h => (hregular h).2 rfl) hn)

end PartialGrid
end AmbidextrousSofa
