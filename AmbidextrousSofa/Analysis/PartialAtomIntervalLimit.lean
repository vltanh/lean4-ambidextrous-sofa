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
  have hatom (j) (hj : fullAngle α (dyadic level) j ∈ Icc a b) :
      (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
        C * (∑ k : AngularGrid.SourceIndex (dyadic level),
          if scaledSource α (dyadic level) k = j then mesh α level else 0) +
          middleOuterMass U α (dyadic level) j +
            selectionDefect target U α level coefficient j := by
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
  calc
    (upperCurvature U).real (Ioc a b) ≤
        ∑ j ∈ Finset.univ.filter (fun j => fullAngle α (dyadic level) j ∈ Icc a b),
          (upperCurvature U {fullAngle α (dyadic level) j}).toReal := by
      rw [AngularGrid.upperCurvature_real_eq_sum_sources hU.isCap (outerGrid α (dyadic level))
        hU.polygon_eq (Ioc_subset_Icc_self.trans hupper) fun ht => htop (Ioc_subset_Icc_self ht)]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.monotone_filter_right _ fun _ _ h => Ioc_subset_Icc_self h)
        fun _ _ _ => ENNReal.toReal_nonneg
    _ ≤ _ := by
      refine (Finset.sum_le_sum fun j hj => hatom j (Finset.mem_filter.mp hj).2).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
      gcongr
      exacts [sum_mesh_scaled_sources_interval_le_of_no_top α level hab htop,
        fun j _ _ => selectionDefect_nonneg target U α level hc j, Finset.subset_univ _]

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
  have hcap n := (hU n).isCap
  have hsigma {t} := MovingSofaOptimality.ang_tendsto_sigmaFun (t := t)
    (fun n => (hcap n).imported_isConvexBody) hTarget.imported_isConvexBody
    (hHausdorff.imported_hausdorffTendsto hcap hTarget)
  have hmiddle := (AngularGrid.middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (grid := fun n => outerGrid α (dyadic (level n))) (fun n => (hU n).polygon_eq) hbox hwidth
    haffine isCompact_Icc hupper fun t ht => (hreg ht).2.2.2).congr
    fun n => Finset.sum_congr (Finset.filter_congr_decidable _ _ _) fun _ _ => rfl
  refine le_of_tendsto_of_tendsto (b := atTop)
    (by simpa only [(hcap _).upperCurvature_real_Ioc hab, hTarget.upperCurvature_real_Ioc hab]
      using (hsigma hb).sub (hsigma ha))
    (by
      have h := (((((mesh_tendsto α).comp hlevel).const_add (b - a)).const_mul C).add hmiddle).add
            (selectionDefect_sum_tendsto (α := α) (level := level) hTarget hcap hc hrate hHausdorff)
      simp only [add_zero] at h
      exact h)
    (hsampled.mono fun n hn => (hU n).curvature_Ioc_le_of_sampled_atom_bound (hc n) hC hab hupper
      (fun h => (hreg h).2.2.1 rfl) (fun h => (hregular h).2 rfl) hn)

end PartialGrid
end AmbidextrousSofa
