module

public import AmbidextrousSofa.Analysis.ShadowCurvature
public import AmbidextrousSofa.Analysis.TangencyLoci

@[expose] public section

/-!
# Actual companion sources below the floor

When the first momentum is positive, the forward neighboring first wall
forces every selected companion source into the upper end of its own
tangent interval. If that interval is below the floor it contains no
source. Moving supporting secants identify its limiting height with the
actual companion tangency. The selected atom errors and their proved
vanishing limits therefore give zero actual companion curvature wherever
the first momentum is positive and that tangency is strictly below zero.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

theorem neighborFeasible_le_firstHi_of_one_separation
    {f g fm fp gm gp δ v : ℝ} (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : g - 1 < companionMinus f gm δ)
    (hv : v ∈ neighborFeasible f g fm fp gm gp δ) :
    v ≤ firstHi f fm δ := by
  have hm : ¬ gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ := fun h =>
    hminus.not_ge (((div_le_iff₀ hc).2 (by linarith)).trans hv.1)
  exact (le_div_iff₀ hs).2 (by linarith [hv.2.1.resolve_right hm])

def secondSelfIntervalTop (U : Set Plane) (t δ : ℝ) : ℝ :=
  (support U (companionNormal t) - 1) * Real.cos t +
    (-forwardAngularSecant U (t + Real.pi / 2) δ + Real.tan (δ / 2)) * Real.sin t

theorem secondSelfIntervalTop_eq_firstHi (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    secondSelfIntervalTop U t δ =
      (support U (companionNormal t) - 1) * Real.cos t +
        firstHi (support U (companionNormal t))
          (support U (companionNormal (t + δ))) δ * Real.sin t := by
  rw [firstHi_eq_secant_add_tan hs hh]
  simp only [secondSelfIntervalTop, forwardAngularSecant, companionNormal_eq_unitNormal,
    show (t + δ) + Real.pi / 2 = (t + Real.pi / 2) + δ by ring,
    ← angleSupport_eq_imported_supp, angleSupport]
  ring

def secondFloorShadowMargin (U : Set Plane) (t δ : ℝ) : ℝ :=
  min (-forwardSecondCornerSecant U t δ - Real.tan (δ / 2))
    (-secondSelfIntervalTop U t δ)

theorem second_source_empty_of_floor_shadow {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    (hmargin : 0 < secondFloorShadowMargin U t.val δ) :
    innerSourceSet U grid (Sum.inr t) = ∅ := by
  have hm := lt_min_iff.mp hmargin
  have htan : 0 < Real.tan δ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hs hc
  have hsep : support U (unitNormal t.val) - 1 <
      companionMinus (support U (companionNormal t.val))
        (support U (unitNormal ((t.val : ℝ) + δ))) δ := by
    linarith [second_companion_forward_shadow_gap U t.val hc.ne' hs.ne' hh, mul_pos htan hm.1]
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨v, hvx, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx
  have hcos : 0 < Real.cos t.val := normal_snd_pos grid (Sum.inr t)
  have hsource := innerSource_height U grid (Sum.inr t) hx
  simp only [normal, supportWall_companionNormal] at hsource
  have hwall : secondWall U t.val x =
      (support U (companionNormal t.val) - 1) * Real.cos t.val + v * Real.sin t.val := by
    rw [secondWall, hvx, div_eq_iff hcos.ne']
    linear_combination (1 - support U (companionNormal t.val)) * Real.sin_sq_add_cos_sq t.val
  have hheight : secondWall U t.val x ≤ secondSelfIntervalTop U t.val δ := by
    rw [hwall, secondSelfIntervalTop_eq_firstHi U t.val hs.ne' hh]
    exact add_le_add_right (mul_le_mul_of_nonneg_right
      (neighborFeasible_le_firstHi_of_one_separation hc hs hsep hv)
      (normal_snd_pos grid (Sum.inl t)).le) _
  linarith [(finiteBarrier_nonneg _ _ _ _ _).trans_eq hsource]

end AngularGrid

theorem CapHausdorffTendsto.secondFloorShadowMargin_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0)
    (htcomp : MovingSofaOptimality.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.secondFloorShadowMargin (U n) (angle n) (δ n)) atTop
      (𝓝 (min (-secondCornerVelocity K t) (-(secondTangency K t).2))) := by
  have hdiv : Tendsto (fun n => δ n / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using hδ.div_const 2
  have hhalf : Tendsto (fun n => Real.tan (δ n / 2)) atTop (𝓝 0) := by
    simpa only [Real.tan_zero, Function.comp_def] using
      (Real.hasDerivAt_tan (x := 0) (by simp)).continuousAt.tendsto.comp hdiv
  -- The top of the self interval tends to the height of the companion tangency.
  have hD : Tendsto (fun n => AngularGrid.secondSelfIntervalTop (U n) (angle n) (δ n)) atTop
      (𝓝 (secondTangency K t).2) := by
    rw [secondTangency_snd_eq_support]
    convert (((h.support_tendsto_moving hU hK ((continuous_companionNormal.tendsto t).comp
      hangle)).sub_const 1).mul ((Real.continuous_cos.tendsto t).comp hangle)).add
      (((h.forwardAngularSecant_tendsto hU hK hB hbox (hangle.add_const (Real.pi / 2)) hδ
        hsin hcos htcomp).neg.add hhalf).mul ((Real.continuous_sin.tendsto t).comp hangle))
      using 2
    · rfl
    · rw [companionNormal_eq_unitNormal]
      simp only [supportTangent, angleSupport, add_zero]
      ring
  simpa only [AngularGrid.secondFloorShadowMargin, sub_zero] using
    ((h.forwardSecondCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht).neg.sub
      hhalf).min hD.neg

namespace AngularGrid

theorem curvature_local_companion_floor_shadow_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c t : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    {ρ : ℝ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s)
    (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ regularCurvatureDomain m) (htop : Real.pi / 2 < t)
    (hpaired : sourceQuarterAngle t ∈ regularCornerDomain m)
    (hp : secondCornerVelocity target (sourceQuarterAngle t) < 0)
    (hD : (secondTangency target (sourceQuarterAngle t)).2 < 0) :
    ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ →
      (upperCurvature target).real (Ioc t (t + d)) ≤ 0 := by
  -- Near `t`, the floor-shadow margins of the selected polygons are eventually positive.
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_uniform_pos_of_moving_tendsto
    (fun n => fullAngle (dyadic (level n)))
    (fun n j => secondFloorShadowMargin (U n)
      (sourceQuarterAngle (fullAngle (dyadic (level n)) j)) (mesh (level n)))
    (lt_min (neg_pos.mpr hp) (neg_pos.mpr hD)) fun ns hns j hangle =>
      CapHausdorffTendsto.secondFloorShadowMargin_tendsto (hHausdorff.comp hns)
        (fun n => (hU (ns n)).isCap) hTarget (isCompact_Icc.prod isCompact_Icc)
        (fun n => hbox (ns n)) (sourceQuarterAngle_tendsto hangle htop.ne')
        (mesh_tendsto.comp (hlevel.comp hns)) (fun _ => mesh_sin_pos _)
        (fun _ => (mesh_cos_pos _).le) (sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.1)
        (sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.2)
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_Ioo.sdiff (toFinite _).isClosed).mem_nhds ht)
  refine ⟨min δ₀ (b - t), lt_min hδ₀ (sub_pos.mpr htIoo.2), fun d hd hdδ => ?_⟩
  have hdδ₀ := hdδ.trans_le (min_le_left _ _)
  have hdb := hdδ.trans_le (min_le_right _ _)
  have hreg : Icc t (t + d) ⊆ regularCurvatureDomain m := fun s hs =>
    hIoo ⟨htIoo.1.trans_le hs.1, by linarith [hs.2]⟩
  simpa only [zero_mul] using curvature_Ioc_le_of_eventual_atom_bound hTarget hU hHausdorff
    hlevel hc hrate hbox hwidth haffine (C := 0) le_rfl (by linarith) hreg
    (sigmaAt_eq_zero_of_density hρ hρ0 heq ht)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq (hreg ⟨by linarith, le_rfl⟩))
    (hfinite.mono fun n hn j hj => by
      have hmargin := hn j (abs_lt.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩)
      -- Every source angle above `π / 2` is a companion source, whose source set is empty.
      cases j with
      | inl s =>
        exact (lt_asymm (interiorPoint_mem (dyadic (level n)) s).2 (htop.trans_le hj.1)).elim
      | inr s =>
        obtain ⟨hm, hp⟩ := dyadic_neighbors (level n) s
        simpa only [zero_mul, zero_add] using (hU n).curvature_atom_le_error_of_source_empty
          (hc n) (Sum.inr s) (second_source_empty_of_floor_shadow (hU n).isCap _ s
            (mesh_cos_pos _) (mesh_sin_pos _) (mesh_half_cos_ne _) hm hp
            (by simpa only [sourceQuarterAngle_fullAngle, Sum.elim_inr] using hmargin)))

end AngularGrid

/-- This is a statement about the actual density of a full maximizer.
The selected polygons, moving source estimates and density
differentiation are all constructed inside the proof. -/
theorem IsFullCapMaximizer.ae_companion_density_zero_of_positive_first_below_floor
    {K : Set Plane} (hK : IsFullCapMaximizer K) {m c C : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      secondCornerVelocity K t < 0 → (secondTangency K t).2 < 0 →
        ρ (t + Real.pi / 2) = 0 := by
  have hR : 0 ≤ |horizontalLeft K| + |horizontalRight K| + 1 := by positivity
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (neg_le_self hR) (subset_symmetricBox_of_horizontalBox
      fun p hp => ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  have h := ae_density_le_of_conditional_local_bound (isOpen_Ioo.sdiff (toFinite _).isClosed)
    hρ hρ0 hρC heq (f := fun _ => 0)
    (P := fun t => Real.pi / 2 < t ∧ sourceQuarterAngle t ∈ regularCornerDomain m ∧
      secondCornerVelocity K (sourceQuarterAngle t) < 0 ∧
        (secondTangency K (sourceQuarterAngle t)).2 < 0) fun t ht hP ε hε => by
      obtain ⟨δ, hδ, hbound⟩ := AngularGrid.curvature_local_companion_floor_shadow_bound
        hK.isCap hU hHausdorff (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate
        (fun n => (hU n).inBox) (by linarith [hK.width_bounds.1, one_lt_M]) haffine hρ hρ0 heq
        ht hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
      exact ⟨δ, hδ, fun d hd hdδ => (hbound d hd hdδ).trans (by positivity)⟩
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet, ae_restrict_of_ae
    ((measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae h)]
    with t ht hz hp hD
  have htop : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith [ht.1.1]
  have hfold : sourceQuarterAngle (t + Real.pi / 2) = t := by simp [sourceQuarterAngle, htop]
  exact le_antisymm (hz ht.2.2 ⟨by linarith [ht.1.1], hfold.symm ▸ ht, hfold.symm ▸ hp,
    hfold.symm ▸ hD⟩) (hρ0 _)

end AmbidextrousSofa
