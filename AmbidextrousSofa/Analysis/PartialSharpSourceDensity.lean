module

public import AmbidextrousSofa.Analysis.PartialSourceVelocity
public import AmbidextrousSofa.Analysis.PartialCurvatureDensity

@[expose] public section

/-!
# Sharp local bounds from the actual proper sampled sources

An interval separated from the top meets at most one of the two
rescaled source families. Its mesh count therefore has the sharp single
interval coefficient. Unsampled nonterminal outer sources have zero
inner mass. The complete middle-facet and selection errors are retained
in the finite bound and vanish before the target bound is asserted.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

open Classical in
theorem sum_mesh_scaled_sources_interval_le_of_no_top (α : TerminalAngle) (n : ℕ)
    {a b : ℝ} (hab : a ≤ b) (htop : Real.pi / 2 ∉ Icc a b) :
    (∑ k : AngularGrid.SourceIndex (dyadic n),
      if fullAngle α (dyadic n) (scaledSource α (dyadic n) k) ∈ Icc a b
        then mesh α n else 0) ≤ b - a + mesh α n := by
  classical
  rw [Fintype.sum_sum_type]
  change (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) ∈ Icc a b then mesh α n else 0) +
    (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) + Real.pi / 2 ∈ Icc a b then mesh α n else 0) ≤ _
  by_cases hb : b < Real.pi / 2
  · have hzero : (∑ t : InteriorPoint (dyadic n),
        if (scaleAngle α t.val : ℝ) + Real.pi / 2 ∈ Icc a b then mesh α n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      apply if_neg
      intro ht
      have hpos := (scaleAngle_mem_open α (interiorPoint_mem (dyadic n) t)).1
      linarith only [ht.2, hpos, hb]
    rw [hzero, add_zero, ← Finset.sum_filter]
    exact sum_mesh_scaled_interior_interval_le α n hab
  · have ha : Real.pi / 2 < a := by
      by_contra hbad
      exact htop ⟨le_of_not_gt hbad, le_of_not_gt hb⟩
    have hzero : (∑ t : InteriorPoint (dyadic n),
        if (scaleAngle α t.val : ℝ) ∈ Icc a b then mesh α n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      apply if_neg
      intro ht
      have hlt := (scaleAngle_mem_open α (interiorPoint_mem (dyadic n) t)).2.trans_le α.property.2
      linarith only [ht.1, hlt, ha]
    rw [hzero, zero_add]
    have hmem (t : InteriorPoint (dyadic n)) :
        (scaleAngle α t.val : ℝ) + Real.pi / 2 ∈ Icc a b ↔
          (scaleAngle α t.val : ℝ) ∈ Icc (a - Real.pi / 2) (b - Real.pi / 2) := by
      constructor <;> intro ht <;> constructor <;> linarith only [ht.1, ht.2]
    simp_rw [hmem]
    rw [← Finset.sum_filter]
    have h := sum_mesh_scaled_interior_interval_le α n
      (show a - Real.pi / 2 ≤ b - Real.pi / 2 by linarith only [hab])
    convert h using 1 <;> ring

open Classical in
/-- Every actual outer atom is counted. Only a sampled interior source
receives a sharp mesh term; the other nonterminal sources keep just
their middle-facet and selection errors. -/
theorem IsSelectedPolygon.curvature_Ioc_le_of_sampled_density
    {target U : Set Plane} {boxLeft boxRight coefficient C a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hC : 0 ≤ C) (hab : a ≤ b)
    (hupper : Icc a b ⊆ Ioo 0 Real.pi) (htop : Real.pi / 2 ∉ Icc a b)
    (hterminal : (α : ℝ) ∉ Icc a b)
    (hdensity : ∀ k : AngularGrid.SourceIndex (dyadic level),
      fullAngle α (dyadic level) (scaledSource α (dyadic level) k) ∈ Icc a b →
        finiteCurvatureDensity (cornerSecant U α level k) (mesh α level) ≤ C * mesh α level) :
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
    by_cases hscaled : ∃ k : AngularGrid.SourceIndex (dyadic level),
        j = scaledSource α (dyadic level) k
    · obtain ⟨k, rfl⟩ := hscaled
      have h := hU.curvature_scaled_atom_refined hc k
      have hb := hdensity k (Finset.mem_filter.mp hj).2
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
        simpa only [if_pos rfl] using h
      linarith only [h, hb, hsingle]
    · have hjterminal : j ≠ terminalIndex α hαL (dyadic level) := by
        intro heq
        apply hterminal
        have hmem := (Finset.mem_filter.mp hj).2
        simpa only [heq, fullAngle, terminalIndex, AngularGrid.fullAngle] using hmem
      have hzero := innerSourceMass_eq_zero_of_not_scaled U α hαL (dyadic level) j
        hjterminal hscaled
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
        hU.polygon_eq (Ioc_subset_Icc_self.trans hupper)
        (fun ht => htop (Ioc_subset_Icc_self ht))
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

theorem curvature_Ioc_le_of_eventual_sampled_density
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
    (hC : 0 ≤ C) (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ Icc a b) (hterminal : (α : ℝ) ∉ Icc a b)
    (hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0)
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0)
    (hdensity : ∀ᶠ n in atTop, ∀ k : AngularGrid.SourceIndex (dyadic (level n)),
      fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) k) ∈ Icc a b →
        finiteCurvatureDensity (cornerSecant (U n) α (level n) k) (mesh α (level n)) ≤
          C * mesh α (level n)) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
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
  have herr := selectionDefect_sum_tendsto (α := α) hTarget hcap hc hrate hHausdorff
  have hmesh := (mesh_tendsto α).comp hlevel
  have hrhs : Tendsto (fun n => C * (b - a + mesh α (level n)) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α (dyadic (level n)) =>
        fullAngle α (dyadic (level n)) j ∈ Icc a b), middleOuterMass (U n) α (dyadic (level n)) j) +
      ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j) atTop
        (𝓝 (C * (b - a))) := by
    simpa only [add_zero] using
      (((tendsto_const_nhds.add hmesh).const_mul C).add hmiddle).add herr
  apply le_of_tendsto_of_tendsto hmass hrhs
  filter_upwards [hdensity] with n hn
  exact (hU n).curvature_Ioc_le_of_sampled_density (hc n) hC hab hupper htop hterminal hn

/-- The source coefficient bounds every sufficiently small interval
about a regular wing normal. It is not assumed continuous. -/
theorem curvature_local_source_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B t ε : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
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
    (ht : t ∈ Ioo A B) (hcomp : MovingSofaOptimality.sigmaAt target (companionSourceAngle t) = 0)
    (hε : 0 < ε) :
    ∃ δ > 0, Ioo (t - δ) (t + δ) ⊆ Ioo A B ∧
      ∀ a b : ℝ, t - δ < a → a ≤ b → b < t + δ →
        (upperCurvature target).real (Ioc a b) ≤
          (sourceKappa (upperCornerVelocity target t) + ε) * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have htnot : t ≠ Real.pi / 2 := fun heq => htop (heq ▸ ht)
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_sampledCurvatureDensity_lt hHausdorff hcap hTarget
    (isCompact_Icc.prod isCompact_Icc) hbox α hlevel htnot hcomp hε
  let δ := min δ₀ (min (t - A) (B - t))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδA : δ ≤ t - A := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ B - t := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Ioo (t - δ) (t + δ) ⊆ Ioo A B := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2, hδA, hδB]
  refine ⟨δ, hδ, hsub, ?_⟩
  intro a b ha hab hb
  have hinterval : Icc a b ⊆ Ioo A B := fun s hs =>
    hsub ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hfree (s : ℝ) (hs : s ∈ Ioo A B) : MovingSofaOptimality.sigmaAt target s = 0 := by
    have hz := curvature_singleton_eq_zero_on_wing hTarget hU hHausdorff hlevel hc hrate
      hR hbox hwidth haffine hA hB htop hterminal hperp hs
    change (upperCurvature target {s}).toReal = 0
    rw [hz, ENNReal.toReal_zero]
  apply curvature_Ioc_le_of_eventual_sampled_density hTarget hU hHausdorff hlevel hc hrate
    hbox hwidth haffine (by linarith only [sourceKappa_nonneg (upperCornerVelocity target t), hε]) hab
    (fun s hs => ⟨hA.trans_lt (hinterval hs).1, (hinterval hs).2.trans_le hB⟩)
    (fun hs => htop (hinterval hs)) (fun hs => hterminal (hinterval hs))
    (fun s hs => hperp s (hinterval hs))
    (hfree a (hinterval ⟨le_rfl, hab⟩)) (hfree b (hinterval ⟨hab, le_rfl⟩))
  filter_upwards [hfinite] with n hn
  intro k hk
  have hnear : |fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) k) - t| < δ₀ := by
    apply abs_lt.mpr
    constructor <;> linarith only [hk.1, hk.2, ha, hb, hδ₀']
  exact (div_le_iff₀ (mesh_pos α (level n))).mp (hn k hnear).le

end PartialGrid

end AmbidextrousSofa
