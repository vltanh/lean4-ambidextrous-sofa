import AmbidextrousSofa.Analysis.ShadowCurvature
import AmbidextrousSofa.Analysis.TangencyLoci

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
  have hm : ¬ gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ := by
    intro h
    have hlow : companionMinus f gm δ ≤ v := by
      change (gm - 1 - (f - 1) * Real.sin δ) / Real.cos δ ≤ v
      rw [div_le_iff₀ hc]
      linarith only [h]
    exact not_lt_of_ge (hlow.trans hv.1) hminus
  have h := hv.2.1.resolve_right hm
  change v ≤ ((f - 1) * Real.cos δ - fm + 1) / Real.sin δ
  rw [le_div_iff₀ hs]
  linarith only [h]

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
    show (t + δ) + Real.pi / 2 = (t + Real.pi / 2) + δ by ring]
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
    have hgap := second_companion_forward_shadow_gap U t.val hc.ne' hs.ne' hh
    have hpositive := mul_pos htan hm.1
    linarith only [hgap, hpositive]
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨v, hvx, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx
  have hvupper := neighborFeasible_le_firstHi_of_one_separation hc hs hsep hv
  have hsin : 0 < Real.sin t.val := normal_snd_pos grid (Sum.inl t)
  have hcos : 0 < Real.cos t.val := normal_snd_pos grid (Sum.inr t)
  have hsource := innerSource_height U grid (Sum.inr t) hx
  simp only [normal, supportWall_companionNormal] at hsource
  have hy0 : 0 ≤ secondWall U t.val x := by
    rw [← hsource]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hwall : secondWall U t.val x =
      (support U (companionNormal t.val) - 1) * Real.cos t.val + v * Real.sin t.val := by
    unfold secondWall
    rw [hvx, div_eq_iff hcos.ne']
    have hcircle := congrArg (fun z : ℝ =>
      (support U (companionNormal t.val) - 1) * z) (Real.sin_sq_add_cos_sq t.val)
    nlinarith only [hcircle]
  have hheight : secondWall U t.val x ≤ secondSelfIntervalTop U t.val δ := by
    rw [hwall, secondSelfIntervalTop_eq_firstHi U t.val hs.ne' hh]
    exact add_le_add_left (mul_le_mul_of_nonneg_right hvupper hsin.le) _
  have hnegative : secondSelfIntervalTop U t.val δ < 0 := neg_pos.mp hm.2
  exact not_lt_of_ge (hy0.trans hheight) hnegative

theorem IsSelectedPolygon.companion_atom_le_error_of_floor_shadow
    {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (t : InteriorPoint (dyadic level))
    (hmargin : 0 < secondFloorShadowMargin U t.val (mesh level)) :
    (upperCurvature U {t.val + Real.pi / 2}).toReal ≤
      middleOuterMass U (dyadic level) (Sum.inr t) +
        selectionDefect target U level coefficient (Sum.inr t) := by
  obtain ⟨hm, hp⟩ := dyadic_neighbors level t
  exact hU.curvature_atom_le_error_of_source_empty hc (Sum.inr t)
    (second_source_empty_of_floor_shadow hU.isCap (dyadic level) t
      (mesh_cos_pos level) (mesh_sin_pos level) (mesh_half_cos_ne level) hm hp hmargin)

end AngularGrid

theorem CapHausdorffTendsto.secondSelfIntervalTop_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : Imported.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.secondSelfIntervalTop (U n) (angle n) (δ n)) atTop
      (𝓝 (secondTangency K t).2) := by
  have hsupp := h.support_tendsto_moving hU hK
    ((continuous_companionNormal.tendsto t).comp hangle)
  have hsec := h.forwardAngularSecant_tendsto hU hK hB hbox
    (hangle.add_const (Real.pi / 2)) hδ hsin hcos ht
  have hdiv : Tendsto (fun n => δ n / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using hδ.div_const 2
  have hhalf : Tendsto (fun n => Real.tan (δ n / 2)) atTop (𝓝 0) := by
    simpa only [Real.tan_zero] using
      (Real.hasDerivAt_tan (x := 0) (by simp)).continuousAt.tendsto.comp hdiv
  have hsinAngle := (Real.continuous_sin.tendsto t).comp hangle
  have hcosAngle := (Real.continuous_cos.tendsto t).comp hangle
  rw [secondTangency_snd_eq_support]
  simpa only [AngularGrid.secondSelfIntervalTop, supportTangent, add_zero,
    companionNormal_eq_unitNormal, add_comm] using
    ((hsupp.sub_const 1).mul hcosAngle).add ((hsec.neg.add hhalf).mul hsinAngle)

theorem CapHausdorffTendsto.secondFloorShadowMargin_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : Imported.sigmaAt K t = 0) (htcomp : Imported.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.secondFloorShadowMargin (U n) (angle n) (δ n)) atTop
      (𝓝 (min (-secondCornerVelocity K t) (-(secondTangency K t).2))) := by
  have hp := h.forwardSecondCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht
  have hD := h.secondSelfIntervalTop_tendsto hU hK hB hbox hangle hδ hsin hcos htcomp
  have hdiv : Tendsto (fun n => δ n / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using hδ.div_const 2
  have hhalf : Tendsto (fun n => Real.tan (δ n / 2)) atTop (𝓝 0) := by
    simpa only [Real.tan_zero] using
      (Real.hasDerivAt_tan (x := 0) (by simp)).continuousAt.tendsto.comp hdiv
  simpa only [AngularGrid.secondFloorShadowMargin, sub_zero] using
    (hp.neg.sub hhalf).min hD.neg

namespace AngularGrid

theorem eventually_companion_floor_shadow_atoms_le
    {target : Set Plane} {U : ℕ → Set Plane} {B : Set Plane}
    {boxLeft boxRight : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {t : ℝ} (htop : Real.pi / 2 < t)
    (ht : Imported.sigmaAt target (sourceQuarterAngle t) = 0)
    (htcomp : Imported.sigmaAt target (sourceQuarterAngle t + Real.pi / 2) = 0)
    (hp : secondCornerVelocity target (sourceQuarterAngle t) < 0)
    (hD : (secondTangency target (sourceQuarterAngle t)).2 < 0) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      |fullAngle (dyadic (level n)) j - t| < δ →
        (upperCurvature (U n) {fullAngle (dyadic (level n)) j}).toReal ≤
          middleOuterMass (U n) (dyadic (level n)) j +
            selectionDefect target (U n) (level n) (coefficient n) j := by
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_uniform_pos_of_moving_tendsto
    (fun n => fullAngle (dyadic (level n)))
    (fun n j => secondFloorShadowMargin (U n)
      (sourceQuarterAngle (fullAngle (dyadic (level n)) j)) (mesh (level n)))
    (lt_min (neg_pos.mpr hp) (neg_pos.mpr hD)) (by
      intro ns hns j hangle
      exact (hHausdorff.comp hns).secondFloorShadowMargin_tendsto
        (fun n => (hU (ns n)).isCap) hTarget hB (fun n => hbox (ns n))
        (sourceQuarterAngle_tendsto hangle (ne_of_gt htop))
        (mesh_tendsto.comp (hlevel.comp hns))
        (fun n => mesh_sin_pos (level (ns n)))
        (fun n => (mesh_cos_pos (level (ns n))).le) ht htcomp)
  let δ := min δ₀ (t - Real.pi / 2)
  have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr htop)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hfinite] with n hn
  intro j hj
  have hmargin := hn j (hj.trans_le (min_le_left _ _))
  have hangle : Real.pi / 2 < fullAngle (dyadic (level n)) j := by
    have hnear := (abs_lt.mp hj).1
    have hgap : δ ≤ t - Real.pi / 2 := min_le_right _ _
    linarith only [hnear, hgap]
  cases j with
  | inl s =>
    have hlt := (interiorPoint_mem (dyadic (level n)) s).2
    change Real.pi / 2 < (s.val : ℝ) at hangle
    exact False.elim (not_lt_of_ge hlt.le hangle)
  | inr s =>
    have hm : 0 < secondFloorShadowMargin (U n) s.val (mesh (level n)) := by
      simpa only [sourceQuarterAngle_fullAngle, Sum.elim_inr] using hmargin
    exact (hU n).companion_atom_le_error_of_floor_shadow (hc n) s hm

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
  have hfirst := sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.1
  have hsecond := sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.2
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_companion_floor_shadow_atoms_le
    hTarget hU hHausdorff hlevel hc (isCompact_Icc.prod isCompact_Icc) hbox
    htop hfirst hsecond hp hD
  have hopen : IsOpen (regularCurvatureDomain m) := by
    rw [regularCurvatureDomain_eq_three]
    exact (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ht)
  let δ := min δ₀ (b - t)
  have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr htIoo.2)
  refine ⟨δ, hδ, ?_⟩
  intro d hd hdδ
  have hreg : Icc t (t + d) ⊆ regularCurvatureDomain m := by
    intro s hs
    apply hIoo
    have hδb : δ ≤ b - t := min_le_right _ _
    exact ⟨htIoo.1.trans_le hs.1, by linarith only [hs.2, hdδ, hδb]⟩
  have hbound := curvature_Ioc_le_of_eventual_atom_bound hTarget hU hHausdorff hlevel hc
    hrate hbox hwidth haffine (C := 0) le_rfl (by linarith only [hd]) hreg
    (sigmaAt_eq_zero_of_density hρ hρ0 heq ht)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq (hreg ⟨by linarith only [hd], le_rfl⟩)) (by
      filter_upwards [hfinite] with n hn
      intro j hj
      have hnear : |fullAngle (dyadic (level n)) j - t| < δ₀ := by
        have hδ₀' : δ ≤ δ₀ := min_le_left _ _
        apply abs_lt.mpr
        constructor <;> linarith only [hj.1, hj.2, hdδ, hδ₀', hδ₀]
      simpa only [zero_mul, zero_add] using hn j hnear)
  simpa only [zero_mul] using hbound

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
  let R := |horizontalLeft K| + |horizontalRight K| + 1
  have hR : 0 ≤ R := by positivity
  have hbox : K ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hK.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hK.isCap.nonempty hK.isCap.isCompact hK.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (by linarith only [hR] : -R ≤ R) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hwidth : 0 < capWidth K := by linarith [hK.width_bounds.1, one_lt_M]
  have hopen : IsOpen (regularCurvatureDomain m) := by
    rw [regularCurvatureDomain_eq_three]
    exact (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  have h := ae_density_le_of_conditional_local_bound hopen hρ hρ0 hρC heq
    (P := fun t => Real.pi / 2 < t ∧ sourceQuarterAngle t ∈ regularCornerDomain m ∧
      secondCornerVelocity K (sourceQuarterAngle t) < 0 ∧
        (secondTangency K (sourceQuarterAngle t)).2 < 0)
    (f := fun _ => 0) (by
      intro t ht hP ε hε
      obtain ⟨δ, hδ, hbound⟩ := AngularGrid.curvature_local_companion_floor_shadow_bound
        hK.isCap hU hHausdorff hlevelTop (fun n => (hc n).le) hrate
        (fun n => (hU n).inBox) hwidth haffine hρ hρ0 heq ht hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
      refine ⟨δ, hδ, ?_⟩
      intro d hd hdδ
      exact (hbound d hd hdδ).trans (by positivity))
  have hshift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae h
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    ae_restrict_of_ae hshift] with t ht hz hp hD
  have htop : Real.pi / 2 < t + Real.pi / 2 := by linarith only [ht.1.1]
  have hfold : sourceQuarterAngle (t + Real.pi / 2) = t := by
    simp only [sourceQuarterAngle, if_neg (not_lt.mpr htop.le), add_sub_cancel_right]
  have hzero : ρ (t + Real.pi / 2) ≤ 0 :=
    hz ht.2.2 ⟨htop, by simpa only [hfold] using ht,
      by simpa only [hfold] using hp, by simpa only [hfold] using hD⟩
  exact le_antisymm hzero (hρ0 _)

end AmbidextrousSofa
