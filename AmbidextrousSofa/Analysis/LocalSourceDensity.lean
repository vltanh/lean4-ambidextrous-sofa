module

public import AmbidextrousSofa.Analysis.SourceVelocity

@[expose] public section

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
  by_contra hnot
  push Not at hnot
  choose ns hns j hangle hvalue using fun k =>
    frequently_atTop.mp (hnot _ (AngularGrid.selectionRate_pos k)) k
  have hangleLim : Tendsto (fun n => angle (ns n) (j n)) atTop (𝓝 t) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun n => norm_nonneg _)
      (fun n => (hangle n).le) AngularGrid.selectionRate_tendsto
  linarith [ge_of_tendsto (hlim ns (tendsto_atTop_mono hns tendsto_id) j hangleLim)
    (Eventually.of_forall hvalue)]

namespace AngularGrid

theorem eventually_sampledCurvatureDensity_lt
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {t ε : ℝ} (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt K (companionSourceAngle t) = 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      |fullAngle (dyadic (level n)) j - t| < δ →
        finiteCurvatureDensity (cornerSecant (U n) (level n) j) (mesh (level n)) /
          mesh (level n) < sourceKappa (upperCornerVelocity K t) + ε :=
  eventually_uniform_upper_of_moving_tendsto (fun n => fullAngle (dyadic (level n)))
    (fun n j => finiteCurvatureDensity (cornerSecant (U n) (level n) j) (mesh (level n)) /
      mesh (level n))
    (fun ns hns j hangle => sampledCurvatureDensity_tendsto (h.comp hns) (fun n => hU (ns n)) hK
      hB (fun n => hbox (ns n)) (hlevel.comp hns) j hangle htop ht) hε

open Classical in
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
  set F := Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
    fullAngle (dyadic level) j ∈ Ioc a b)
  have hFG : F ⊆ Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
      fullAngle (dyadic level) j ∈ Icc a b) :=
    Finset.monotone_filter_right _ fun _ _ h => Ioc_subset_Icc_self h
  rw [upperCurvature_real_eq_sum_sources hU.isCap (dyadic level) hU.polygon_eq
    (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))]
  calc _ ≤ ∑ j ∈ F, (C * mesh level + middleOuterMass U (dyadic level) j +
        selectionDefect target U level coefficient j) := Finset.sum_le_sum fun j hj => by
          linarith [hU.curvature_atom_refined hc j, hdensity j (Finset.mem_filter.mp (hFG hj)).2]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      gcongr C * ?_ + ?_ + ?_
      · exact (Finset.sum_le_sum_of_subset_of_nonneg hFG fun _ _ _ => (mesh_pos level).le).trans
          (sum_mesh_interval_sources_le level hab)
      · exact Finset.sum_le_sum_of_subset_of_nonneg hFG fun j _ _ =>
          middleOuterMass_nonneg hU.isCap _ j
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ =>
          selectionDefect_nonneg target U level hc j

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
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0)
    (hdensity : ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      fullAngle (dyadic (level n)) j ∈ Icc a b →
        finiteCurvatureDensity (cornerSecant (U n) (level n) j) (mesh (level n)) ≤
          C * mesh (level n)) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  refine le_of_tendsto_of_tendsto ?_ ?_ (hdensity.mono fun n hn =>
    (hU n).curvature_Ioc_le_of_sampled_density (hc n) hC hab hupper htop hn)
  · simpa only [(hcap _).upperCurvature_real_Ioc hab, hTarget.upperCurvature_real_Ioc hab] using
      (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb).sub
        (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha)
  · have hmiddle := middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
      (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
    convert ((((tendsto_const_nhds (x := b - a)).add (mesh_tendsto.comp hlevel)).const_mul C).add
      hmiddle).add (selectionDefect_sum_tendsto hTarget hcap hc hrate hHausdorff) using 6 <;> simp

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
    (ht : t ∈ Ioo A B) (hcomp : MovingSofaOptimality.sigmaAt target (companionSourceAngle t) = 0)
    (hε : 0 < ε) :
    ∃ δ > 0, Ioo (t - δ) (t + δ) ⊆ Ioo A B ∧
      ∀ a b : ℝ, t - δ < a → a ≤ b → b < t + δ →
        (upperCurvature target).real (Ioc a b) ≤
          (sourceKappa (upperCornerVelocity target t) + ε) * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_sampledCurvatureDensity_lt hHausdorff hcap hTarget
    (isCompact_Icc.prod isCompact_Icc) hbox hlevel (fun heq => htop (heq ▸ ht)) hcomp hε
  obtain ⟨δ, hδ, hδ₀', hδA, hδB⟩ : ∃ δ > 0, δ ≤ δ₀ ∧ δ ≤ t - A ∧ δ ≤ B - t :=
    ⟨_, lt_min hδ₀ (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)), min_le_left _ _,
      le_min_iff.mp (min_le_right _ _)⟩
  have hsub : Ioo (t - δ) (t + δ) ⊆ Ioo A B := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨δ, hδ, hsub, fun a b ha hab hb => ?_⟩
  have hinterval : Icc a b ⊆ Ioo A B := fun s hs => hsub ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hfree (s : ℝ) (hs : s ∈ Icc a b) : MovingSofaOptimality.sigmaAt target s = 0 :=
    (congrArg ENNReal.toReal (curvature_singleton_eq_zero_on_wing hTarget hU hHausdorff hlevel hc
      hrate hR hbox hwidth haffine hA hB htop hperp (hinterval hs))).trans ENNReal.toReal_zero
  refine curvature_Ioc_le_of_eventual_sampled_density hTarget hU hHausdorff hlevel hc hrate
    hbox hwidth haffine (by linarith [sourceKappa_nonneg (upperCornerVelocity target t)]) hab
    (fun s hs => ⟨hA.trans_lt (hinterval hs).1, (hinterval hs).2.trans_le hB⟩)
    (fun hs => htop (hinterval hs)) (fun s hs => hperp s (hinterval hs))
    (hfree a ⟨le_rfl, hab⟩) (hfree b ⟨hab, le_rfl⟩) (hfinite.mono fun n hn j hj => ?_)
  exact (div_le_iff₀ (mesh_pos (level n))).mp
    (hn j (abs_lt.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩)).le

end AngularGrid

end AmbidextrousSofa
