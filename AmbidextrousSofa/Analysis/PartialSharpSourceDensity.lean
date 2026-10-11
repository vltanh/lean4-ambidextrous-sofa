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
  have hs (t : InteriorPoint (dyadic n)) := scaleAngle_mem_open α (interiorPoint_mem (dyadic n) t)
  have h1 := sum_mesh_scaled_interior_interval_le α n hab
  have h2 := sum_mesh_scaled_interior_interval_le α n (sub_le_sub_right hab (Real.pi / 2))
  simp only [Finset.sum_filter, ← Set.add_mem_Icc_iff_left, sub_sub_sub_cancel_right] at h1 h2
  rcases lt_or_ge b (Real.pi / 2) with hb | hb
  · have h (t : InteriorPoint (dyadic n)) : (scaleAngle α t.val : ℝ) + Real.pi / 2 ∉ Icc a b :=
      fun ht => by linarith [ht.2, (hs t).1]
    simpa only [h, ↓reduceIte, Finset.sum_const_zero, add_zero] using h1
  · have h (t : InteriorPoint (dyadic n)) : (scaleAngle α t.val : ℝ) ∉ Icc a b :=
      fun ht => htop ⟨by linarith [ht.1, (hs t).2, α.property.2], hb⟩
    simpa only [h, ↓reduceIte, Finset.sum_const_zero, zero_add] using h2

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
  have hδ := (mesh_pos α level).le
  -- The sharp mesh term of `j`: present exactly when `j` is a sampled source.
  have hw (j : SourceIndex α (dyadic level)) (k : AngularGrid.SourceIndex (dyadic level)) :
      0 ≤ if scaledSource α (dyadic level) k = j then C * mesh α level else 0 := by positivity
  refine (hU.curvature_set_le_of_atoms hc (Ioc_subset_Icc_self.trans hupper)
    (fun ht => htop (Ioc_subset_Icc_self ht)) Ioc_subset_Icc_self
    (fun j => Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hw j k) fun j hj => ?_).trans ?_
  · by_cases hscaled : ∃ k : AngularGrid.SourceIndex (dyadic level),
        j = scaledSource α (dyadic level) k
    · obtain ⟨k, rfl⟩ := hscaled
      have hk := Finset.single_le_sum (fun q _ => hw (scaledSource α (dyadic level) k) q)
        (Finset.mem_univ k)
      simp only [↓reduceIte] at hk
      linarith [hU.curvature_scaled_atom_refined hc k, hdensity k (Ioc_subset_Icc_self hj)]
    · have h := hU.curvature_atom_le_mass hc j
      rw [innerSourceMass_eq_zero_of_not_scaled U α hαL (dyadic level) j
        (fun h => hterminal (by subst h; exact Ioc_subset_Icc_self hj)) hscaled] at h
      linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hw j k]
  rw [Finset.sum_comm]
  gcongr ?_ + _ + _
  simpa only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mul_sum, mul_ite, mul_zero] using
    mul_le_mul_of_nonneg_left (sum_mesh_scaled_sources_interval_le_of_no_top α level hab htop) hC

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
    have hK := hTarget.imported_isConvexBody
    simpa only [fun n => (hcap n).upperCurvature_real_Ioc hab, hTarget.upperCurvature_real_Ioc hab]
      using (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hK hlim hb).sub
        (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hK hlim ha)
  refine le_of_tendsto_of_tendsto hmass ?_ (hdensity.mono fun n hn =>
    (hU n).curvature_Ioc_le_of_sampled_density (hc n) hC hab hupper htop hterminal hn)
  have hmiddle := AngularGrid.middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (grid := fun n => outerGrid α (dyadic (level n)))
    (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
  convert (((tendsto_const_nhds.add ((mesh_tendsto α).comp hlevel)).const_mul C).add
    hmiddle).add (selectionDefect_sum_tendsto (α := α) hTarget hcap hc hrate hHausdorff) using 6 <;>
    first | rfl | simp

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
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_sampledCurvatureDensity_lt hHausdorff
    (fun n => (hU n).isCap) hTarget (isCompact_Icc.prod isCompact_Icc) hbox α hlevel
    (fun h => htop (h ▸ ht)) hcomp hε
  have h1 := min_le_left δ₀ (min (t - A) (B - t))
  have h2 := (min_le_right δ₀ _).trans (min_le_left (t - A) (B - t))
  have h3 := (min_le_right δ₀ _).trans (min_le_right (t - A) (B - t))
  have hsub : Ioo (t - min δ₀ (min (t - A) (B - t))) (t + min δ₀ (min (t - A) (B - t))) ⊆
      Ioo A B := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨_, lt_min hδ₀ (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)), hsub,
    fun a b ha hab hb => ?_⟩
  have hinterval : Icc a b ⊆ Ioo A B := fun s hs => hsub ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hfree (s : ℝ) (hs : s ∈ Ioo A B) : MovingSofaOptimality.sigmaAt target s = 0 :=
    (congrArg ENNReal.toReal (curvature_singleton_eq_zero_on_wing hTarget hU hHausdorff hlevel hc
      hrate hR hbox hwidth haffine hA hB htop hterminal hperp hs)).trans ENNReal.toReal_zero
  exact curvature_Ioc_le_of_eventual_sampled_density hTarget hU hHausdorff hlevel hc hrate
    hbox hwidth haffine (by linarith [sourceKappa_nonneg (upperCornerVelocity target t)]) hab
    (fun s hs => ⟨hA.trans_lt (hinterval hs).1, (hinterval hs).2.trans_le hB⟩)
    (fun hs => htop (hinterval hs)) (fun hs => hterminal (hinterval hs))
    (fun s hs => hperp s (hinterval hs))
    (hfree a (hinterval ⟨le_rfl, hab⟩)) (hfree b (hinterval ⟨hab, le_rfl⟩))
    (hfinite.mono fun n hn k hk => (div_le_iff₀ (mesh_pos α (level n))).mp
      (hn k (abs_lt.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩)).le)

end PartialGrid

end AmbidextrousSofa
