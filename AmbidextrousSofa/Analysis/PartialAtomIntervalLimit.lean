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
  classical
  let F := Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
    fullAngle α (dyadic level) j ∈ Ioc a b)
  let G := Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
    fullAngle α (dyadic level) j ∈ Icc a b)
  have hδ : 0 ≤ mesh α level := (mesh_pos α level).le
  have hFG : F ⊆ G := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ioc_subset_Icc_self (Finset.mem_filter.mp hj).2⟩
  have hatom (j : SourceIndex α (dyadic level)) (hj : j ∈ G) :
      (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
        (∑ k : AngularGrid.SourceIndex (dyadic level),
          if scaledSource α (dyadic level) k = j then C * mesh α level else 0) +
          middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j := by
    by_cases hscaled : ∃ k : AngularGrid.SourceIndex (dyadic level), j = scaledSource α (dyadic level) k
    · obtain ⟨k, rfl⟩ := hscaled
      have h := hsampled k (Finset.mem_filter.mp hj).2
      have hsingle : C * mesh α level ≤
          ∑ q : AngularGrid.SourceIndex (dyadic level),
            if scaledSource α (dyadic level) q = scaledSource α (dyadic level) k
              then C * mesh α level else 0 := by
        have h := Finset.single_le_sum
          (fun q (_ : q ∈ (Finset.univ : Finset (AngularGrid.SourceIndex (dyadic level)))) =>
            show 0 ≤ (if scaledSource α (dyadic level) q = scaledSource α (dyadic level) k
              then C * mesh α level else 0) from by
                split_ifs
                · exact mul_nonneg hC hδ
                · exact le_rfl)
          (Finset.mem_univ k)
        simpa only [↓reduceIte] using h
      linarith only [h, hsingle]
    · have hjterminal : j ≠ terminalIndex α hαL (dyadic level) := by
        intro heq
        apply hterminal
        have hmem := (Finset.mem_filter.mp hj).2
        rw [heq] at hmem
        exact hmem
      have hzero := innerSourceMass_eq_zero_of_not_scaled U α hαL (dyadic level) j hjterminal hscaled
      have h := hU.curvature_atom_le_mass hc j
      rw [hzero, zero_add] at h
      have hsum : 0 ≤ ∑ k : AngularGrid.SourceIndex (dyadic level),
          if scaledSource α (dyadic level) k = j then C * mesh α level else 0 := by
        apply Finset.sum_nonneg
        intro k _
        split_ifs
        · exact mul_nonneg hC hδ
        · exact le_rfl
      linarith only [h, hsum]
  have hmain : (∑ j ∈ G, ∑ k : AngularGrid.SourceIndex (dyadic level),
        if scaledSource α (dyadic level) k = j then C * mesh α level else 0) =
      C * ∑ k : AngularGrid.SourceIndex (dyadic level),
        if fullAngle α (dyadic level) (scaledSource α (dyadic level) k) ∈ Icc a b
          then mesh α level else 0 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_ite_eq]
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp only [mul_zero]
  have herr : (∑ j ∈ G, selectionDefect target U α level coefficient j) ≤
      ∑ j, selectionDefect target U α level coefficient j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => selectionDefect_nonneg target U α level hc j)
  have hcount := mul_le_mul_of_nonneg_left
    (sum_mesh_scaled_sources_interval_le_of_no_top α level hab htop) hC
  calc
    (upperCurvature U).real (Ioc a b) =
        ∑ j ∈ F, (upperCurvature U {fullAngle α (dyadic level) j}).toReal :=
      AngularGrid.upperCurvature_real_eq_sum_sources hU.isCap (outerGrid α (dyadic level))
        hU.polygon_eq (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))
    _ ≤ ∑ j ∈ G, (upperCurvature U {fullAngle α (dyadic level) j}).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => ENNReal.toReal_nonneg)
    _ ≤ ∑ j ∈ G, ((∑ k : AngularGrid.SourceIndex (dyadic level),
        if scaledSource α (dyadic level) k = j then C * mesh α level else 0) +
        middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j) :=
      Finset.sum_le_sum hatom
    _ = C * (∑ k : AngularGrid.SourceIndex (dyadic level),
        if fullAngle α (dyadic level) (scaledSource α (dyadic level) k) ∈ Icc a b
          then mesh α level else 0) +
        (∑ j ∈ G, middleOuterMass U α (dyadic level) j) +
        ∑ j ∈ G, selectionDefect target U α level coefficient j := by
      simp only [Finset.sum_add_distrib, hmain]
    _ ≤ _ := add_le_add (add_le_add hcount le_rfl) herr

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
  have htop : Real.pi / 2 ∉ Icc a b := by
    intro h
    exact (mem_regularCurvatureDomain_iff.mp (hregular h).1).2.2.1 rfl
  have hterminal : (α : ℝ) ∉ Icc a b := fun h => (hregular h).2 rfl
  have hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0 :=
    fun t ht => (mem_regularCurvatureDomain_iff.mp (hregular ht).1).2.2.2
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc a b)) atTop
      (𝓝 ((upperCurvature target).real (Ioc a b))) := by
    have hleft := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha
    have hright := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb
    have hFormula (n : ℕ) := (hcap n).upperCurvature_real_Ioc hab
    simpa only [hFormula, hTarget.upperCurvature_real_Ioc hab] using hright.sub hleft
  have hmiddle := AngularGrid.middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (grid := fun n => outerGrid α (dyadic (level n)))
    (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
  have herr := selectionDefect_sum_tendsto (α := α) (level := level) hTarget hcap hc hrate hHausdorff
  have hmesh := (mesh_tendsto α).comp hlevel
  have hrhs : Tendsto (fun n => C * (b - a + mesh α (level n)) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α (dyadic (level n)) =>
        fullAngle α (dyadic (level n)) j ∈ Icc a b), middleOuterMass (U n) α (dyadic (level n)) j) +
      ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j) atTop (𝓝 (C * (b - a))) := by
    have hmiddle' : Tendsto (fun n => ∑ j ∈ Finset.univ.filter
        (fun j : SourceIndex α (dyadic (level n)) => fullAngle α (dyadic (level n)) j ∈ Icc a b),
          middleOuterMass (U n) α (dyadic (level n)) j) atTop (𝓝 0) := by
      refine hmiddle.congr (fun n => Finset.sum_congr ?_ (fun j _ => rfl))
      exact Finset.filter_congr_decidable _ _ _
    have hconst : Tendsto (fun _ : ℕ => b - a) atTop (𝓝 (b - a)) := tendsto_const_nhds
    have h := (((hconst.add hmesh).const_mul C).add hmiddle').add herr
    simp only [add_zero] at h
    exact h
  apply le_of_tendsto_of_tendsto hmass hrhs
  filter_upwards [hsampled] with n hn
  exact (hU n).curvature_Ioc_le_of_sampled_atom_bound (hc n) hC hab hupper htop hterminal hn

end PartialGrid
end AmbidextrousSofa
