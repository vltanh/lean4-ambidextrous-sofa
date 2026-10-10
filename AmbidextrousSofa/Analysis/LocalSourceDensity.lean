import AmbidextrousSofa.Analysis.SourceVelocity

/-!
# Local sharp curvature bounds from the actual sampled sources

A sequential compactness argument upgrades convergence along every
moving sample to a uniform upper bound near a fixed normal. Summing the
actual selected facet inequality retains the middle and penalty errors;
their proved limits then yield a sharp bound on every sufficiently small
target interval. The normal at which the bound is centered only needs a
non-atomic companion face.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- A local upper bound follows from convergence along every moving
sample and every diverging subsequence. The sample types may vary with
the stage and may be empty. -/
theorem eventually_uniform_upper_of_moving_tendsto
    {J : ℕ → Type*} (angle value : ∀ n, J n → ℝ) {t L : ℝ}
    (hlim : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∀ j : ∀ n, J (ns n),
        Tendsto (fun n => angle (ns n) (j n)) atTop (𝓝 t) →
        Tendsto (fun n => value (ns n) (j n)) atTop (𝓝 L))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : J n,
      |angle n j - t| < δ → value n j < L + ε := by
  classical
  by_contra hnot
  have hfail : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ ∃ j : J n,
      |angle n j - t| < AngularGrid.selectionRate k ∧ L + ε ≤ value n j := by
    intro k
    by_contra hnone
    apply hnot
    refine ⟨AngularGrid.selectionRate k, AngularGrid.selectionRate_pos k,
      eventually_atTop.mpr ⟨k, ?_⟩⟩
    intro n hn j hj
    apply lt_of_not_ge
    intro hv
    exact hnone ⟨n, hn, j, hj, hv⟩
  choose ns hns j hangle hvalue using hfail
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hangleLim : Tendsto (fun n => angle (ns n) (j n)) atTop (𝓝 t) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using
      squeeze_zero (fun n => abs_nonneg (angle (ns n) (j n) - t))
        (fun n => (hangle n).le) AngularGrid.selectionRate_tendsto
  have hbound : L + ε ≤ L :=
    ge_of_tendsto (hlim ns hnsTop j hangleLim) (Eventually.of_forall hvalue)
  linarith

namespace AngularGrid

theorem eventually_sampledCurvatureDensity_lt
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {t ε : ℝ} (htop : t ≠ Real.pi / 2)
    (ht : Imported.sigmaAt K (companionSourceAngle t) = 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      |fullAngle (dyadic (level n)) j - t| < δ →
        finiteCurvatureDensity (cornerSecant (U n) (level n) j) (mesh (level n)) /
          mesh (level n) < sourceKappa (upperCornerVelocity K t) + ε := by
  apply eventually_uniform_upper_of_moving_tendsto
    (fun n => fullAngle (dyadic (level n)))
    (fun n j => finiteCurvatureDensity (cornerSecant (U n) (level n) j) (mesh (level n)) /
      mesh (level n)) ?_ hε
  intro ns hns j hangle
  exact sampledCurvatureDensity_tendsto (h.comp hns) (fun n => hU (ns n)) hK hB
    (fun n => hbox (ns n)) (hlevel.comp hns) j hangle htop ht

theorem IsSelectedPolygon.curvature_Ioc_le_of_sampled_density
    {target U : Set Plane} {boxLeft boxRight coefficient C a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hC : 0 ≤ C) (hab : a ≤ b)
    (hupper : Icc a b ⊆ Ioo 0 Real.pi) (htop : Real.pi / 2 ∉ Icc a b)
    (hdensity : ∀ j : SourceIndex (dyadic level), fullAngle (dyadic level) j ∈ Icc a b →
      finiteCurvatureDensity (cornerSecant U level j) (mesh level) ≤ C * mesh level) :
    (upperCurvature U).real (Ioc a b) ≤
      C * (b - a + mesh level) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
        fullAngle (dyadic level) j ∈ Icc a b), middleOuterMass U (dyadic level) j) +
      ∑ j, selectionDefect target U level coefficient j := by
  classical
  let F := Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
    fullAngle (dyadic level) j ∈ Ioc a b)
  let G := Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
    fullAngle (dyadic level) j ∈ Icc a b)
  have hFG : F ⊆ G := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Ioc_subset_Icc_self (Finset.mem_filter.mp hj).2⟩
  have hcount : (∑ j ∈ F, mesh level) ≤ b - a + mesh level := by
    apply le_trans ?_ (sum_mesh_interval_sources_le level hab)
    exact Finset.sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => (mesh_pos level).le)
  have hmid : (∑ j ∈ F, middleOuterMass U (dyadic level) j) ≤
      ∑ j ∈ G, middleOuterMass U (dyadic level) j :=
    Finset.sum_le_sum_of_subset_of_nonneg hFG
      (fun j _ _ => middleOuterMass_nonneg hU.isCap (dyadic level) j)
  have herr : (∑ j ∈ F, selectionDefect target U level coefficient j) ≤
      ∑ j, selectionDefect target U level coefficient j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => selectionDefect_nonneg target U level hc j)
  have hatom (j : SourceIndex (dyadic level)) (hj : j ∈ F) :
      (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
        C * mesh level + middleOuterMass U (dyadic level) j +
          selectionDefect target U level coefficient j := by
    have h := hU.curvature_atom_refined hc j
    have hbound := hdensity j (Finset.mem_filter.mp (hFG hj)).2
    linarith
  calc
    (upperCurvature U).real (Ioc a b) =
        ∑ j ∈ F, (upperCurvature U {fullAngle (dyadic level) j}).toReal :=
      upperCurvature_real_eq_sum_sources hU.isCap (dyadic level) hU.polygon_eq
        (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))
    _ ≤ ∑ j ∈ F, (C * mesh level + middleOuterMass U (dyadic level) j +
        selectionDefect target U level coefficient j) := Finset.sum_le_sum hatom
    _ = C * (∑ j ∈ F, mesh level) +
        (∑ j ∈ F, middleOuterMass U (dyadic level) j) +
          ∑ j ∈ F, selectionDefect target U level coefficient j := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hcount hC) hmid) herr

/-- The complete actual error terms vanish before the interval bound is
asserted for the target. -/
theorem curvature_Ioc_le_of_eventual_sampled_density
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
    (hC : 0 ≤ C) (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ Icc a b)
    (hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0)
    (ha : Imported.sigmaAt target a = 0) (hb : Imported.sigmaAt target b = 0)
    (hdensity : ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      fullAngle (dyadic (level n)) j ∈ Icc a b →
        finiteCurvatureDensity (cornerSecant (U n) (level n) j) (mesh (level n)) ≤
          C * mesh (level n)) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, Imported.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc a b)) atTop
      (𝓝 ((upperCurvature target).real (Ioc a b))) := by
    have hleft := Imported.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha
    have hright := Imported.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb
    have hFormula (n : ℕ) := (hcap n).upperCurvature_real_Ioc hab
    simpa only [hFormula, hTarget.upperCurvature_real_Ioc hab] using hright.sub hleft
  have hmiddle := middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
  have herr := selectionDefect_sum_tendsto hTarget hcap hc hrate hHausdorff
  have hmesh := mesh_tendsto.comp hlevel
  have hrhs : Tendsto (fun n => C * (b - a + mesh (level n)) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic (level n)) =>
        fullAngle (dyadic (level n)) j ∈ Icc a b), middleOuterMass (U n) (dyadic (level n)) j) +
      ∑ j, selectionDefect target (U n) (level n) (coefficient n) j) atTop
        (𝓝 (C * (b - a))) := by
    simpa only [add_zero] using
      (((tendsto_const_nhds.add hmesh).const_mul C).add hmiddle).add herr
  apply le_of_tendsto_of_tendsto hmass hrhs
  filter_upwards [hdensity] with n hn
  exact (hU n).curvature_Ioc_le_of_sampled_density (hc n) hC hab hupper htop hn

/-- At every wing normal whose companion face is a singleton, arbitrarily
small intervals have curvature at most the local sharp coefficient times
their length. -/
theorem curvature_local_source_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B t ε : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ s ∈ Ioo A B, Real.cos s + m * Real.sin s ≠ 0)
    (ht : t ∈ Ioo A B) (hcomp : Imported.sigmaAt target (companionSourceAngle t) = 0)
    (hε : 0 < ε) :
    ∃ δ > 0, Ioo (t - δ) (t + δ) ⊆ Ioo A B ∧
      ∀ a b : ℝ, t - δ < a → a ≤ b → b < t + δ →
        (upperCurvature target).real (Ioc a b) ≤
          (sourceKappa (upperCornerVelocity target t) + ε) * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have htnot : t ≠ Real.pi / 2 := fun heq => htop (heq ▸ ht)
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_sampledCurvatureDensity_lt hHausdorff hcap hTarget
    (isCompact_Icc.prod isCompact_Icc) hbox hlevel htnot hcomp hε
  let δ := min δ₀ (min (t - A) (B - t))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδA : δ ≤ t - A := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ B - t := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Ioo (t - δ) (t + δ) ⊆ Ioo A B := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  refine ⟨δ, hδ, hsub, ?_⟩
  intro a b ha hab hb
  have hinterval : Icc a b ⊆ Ioo A B := fun s hs =>
    hsub ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hfree (s : ℝ) (hs : s ∈ Ioo A B) : Imported.sigmaAt target s = 0 := by
    have hz := curvature_singleton_eq_zero_on_wing hTarget hU hHausdorff hlevel hc hrate
      hR hbox hwidth haffine hA hB htop hperp hs
    change (upperCurvature target {s}).toReal = 0
    rw [hz, ENNReal.toReal_zero]
  apply curvature_Ioc_le_of_eventual_sampled_density hTarget hU hHausdorff hlevel hc hrate
    hbox hwidth haffine (by linarith [sourceKappa_nonneg (upperCornerVelocity target t)]) hab
    (fun s hs => ⟨hA.trans_lt (hinterval hs).1, (hinterval hs).2.trans_le hB⟩)
    (fun hs => htop (hinterval hs)) (fun s hs => hperp s (hinterval hs))
    (hfree a (hinterval ⟨le_rfl, hab⟩)) (hfree b (hinterval ⟨hab, le_rfl⟩))
  filter_upwards [hfinite] with n hn
  intro j hj
  have hnear : |fullAngle (dyadic (level n)) j - t| < δ₀ := by
    apply abs_lt.mpr
    constructor <;> linarith [hj.1, hj.2]
  exact (div_le_iff₀ (mesh_pos (level n))).mp (hn j hnear).le

end AngularGrid

end AmbidextrousSofa
