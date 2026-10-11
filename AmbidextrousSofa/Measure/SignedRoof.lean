module

public import AmbidextrousSofa.Measure.SupportArea

@[expose] public section

/-!
# Actual tangent and corner pieces of a swept niche

Curvature at most one means that the complementary profiles `1-f` and `1-g`
have nonnegative curvature. Their support inequalities therefore give global
wall bounds at the tangent points. Momentum signs select actual tangent and
corner contacts of the complete angular supremum. No sampled-angle or local
stationarity assertion is used in place of global exposure.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem firstTangent_dominates_support {f fD fDD : ℝ → ℝ}
    (hf : Continuous f) (hfD : Continuous fD)
    (hderiv : ∀ t, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hsecond : ∀ t, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hcurv : ∀ t ∈ Icc 0 (Real.pi / 2), f t + fDD t ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    f t - 1 ≤ coordDot (firstTangentPoint f fD s) (unitNormal t) := by
  have h := Reference.supportProjection_le_self (h := fun x => 1 - f x) (hD := fun x => -fD x)
    (hDD := fun x => -fDD x) (continuous_const.sub hf) hfD.neg
    (fun x => (hderiv x).const_sub 1) (fun x => (hsecond x).neg)
    (fun x hx => by linarith [hcurv x hx]) (by linarith [Real.pi_pos]) hs ht
  rw [firstTangentPoint, Reference.coordDot_supportPoint]
  simp only [Reference.supportProjection] at h ⊢
  linarith

theorem secondTangent_dominates_support {g gD gDD : ℝ → ℝ}
    (hg : Continuous g) (hgD : Continuous gD)
    (hderiv : ∀ t, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecond : ∀ t, HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hcurv : ∀ t ∈ Icc 0 (Real.pi / 2), g t + gDD t ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t) := by
  rw [secondTangentPoint, companionNormal_eq_unitNormal, Reference.coordDot_companionSupportPoint,
    add_sub_cancel_right, ← Reference.coordDot_supportPoint]
  exact firstTangent_dominates_support hg hgD hderiv hsecond hcurv hs ht

theorem innerCorner_dot_eq_firstTangent (f g fD : ℝ → ℝ) (s t : ℝ) :
    coordDot (innerCornerPoint f g s) (unitNormal t) =
      coordDot (firstTangentPoint f fD s) (unitNormal t) -
        supportP fD g s * Real.sin (t - s) := by
  unfold coordDot innerCornerPoint firstTangentPoint Reference.supportPoint unitNormal supportP
  rw [Real.sin_sub]
  ring

theorem innerCorner_dot_eq_secondTangent (f g gD : ℝ → ℝ) (s t : ℝ) :
    coordDot (innerCornerPoint f g s) (companionNormal t) =
      coordDot (secondTangentPoint g gD s) (companionNormal t) +
        supportQ gD f s * Real.sin (s - t) := by
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  unfold coordDot innerCornerPoint companionNormal supportQ
  rw [Real.sin_sub]
  ring

theorem innerCorner_snd_eq_firstTangent (f g fD : ℝ → ℝ) (s : ℝ) :
    (innerCornerPoint f g s).2 = (firstTangentPoint f fD s).2 -
      supportP fD g s * Real.cos s := by
  unfold innerCornerPoint firstTangentPoint Reference.supportPoint supportP
  ring

/-- A point above the walls of every interior angle and below both walls of one
interior angle lies on the swept niche. -/
theorem sweptNiche_eq_of_global_contact {U : Set Plane} (hU : IsCompact U) {f g : ℝ → ℝ}
    (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    {p : Plane} (hp : 0 ≤ p.2)
    (hbound : ∀ t ∈ Ioo 0 (Real.pi / 2),
      f t - 1 ≤ coordDot p (unitNormal t) ∨ g t - 1 ≤ coordDot p (companionNormal t))
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2)) (h1 : coordDot p (unitNormal s) ≤ f s - 1)
    (h2 : coordDot p (companionNormal s) ≤ g s - 1) :
    sweptNiche U (Real.pi / 2) p.1 = p.2 := by
  have hsc : ∀ t ∈ Ioo 0 (Real.pi / 2), 0 < Real.sin t ∧ 0 < Real.cos t := fun t ht =>
    sin_cos_pos_of_mem_quarter ht
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) hp fun t ht => ?_)
    (le_trans ?_ (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU le_rfl p.1) hs))
  · rw [cornerWall_le_iff (hsc t ht).1 (hsc t ht).2, hF t (Ioo_subset_Icc_self ht),
      hG t (Ioo_subset_Icc_self ht)]
    exact hbound t ht
  · have := hF s (Ioo_subset_Icc_self hs)
    have := hG s (Ioo_subset_Icc_self hs)
    simp only [coordDot, unitNormal, companionNormal] at h1 h2
    exact le_min ((le_div_iff₀ (hsc s hs).1).2 (by linarith))
      ((le_div_iff₀ (hsc s hs).2).2 (by linarith))

/-- Every tangent point with the indicated contact sign is exposed by the
whole angular supremum. The dominance hypothesis is proved above from `ρ≤1`. -/
theorem sweptNiche_firstTangent {U : Set Plane} (hU : IsCompact U)
    {f g fD : ℝ → ℝ} (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hFtop : f (Real.pi / 2) = 1) {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2))
    (hp : supportP fD g s ≤ 0)
    (hdom : ∀ t ∈ Icc 0 (Real.pi / 2),
      f t - 1 ≤ coordDot (firstTangentPoint f fD s) (unitNormal t)) :
    sweptNiche U (Real.pi / 2) (firstTangentPoint f fD s).1 =
      (firstTangentPoint f fD s).2 := by
  refine sweptNiche_eq_of_global_contact hU hF hG ?_
    (fun t ht => .inl (hdom t (Ioo_subset_Icc_self ht))) hs ?_ ?_
  · simpa [hFtop, coordDot, unitNormal] using hdom _ ⟨by positivity, le_rfl⟩
  · rw [firstTangentPoint, Reference.coordDot_supportPoint, Reference.supportProjection_self]
  · rw [firstTangentPoint, companionNormal_eq_unitNormal, Reference.coordDot_supportPoint]
    simp [Reference.supportProjection]
    linarith [show fD s - g s + 1 ≤ 0 from hp]

theorem sweptNiche_secondTangent {U : Set Plane} (hU : IsCompact U)
    {f g gD : ℝ → ℝ} (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hGtop : g 0 = 1) {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2))
    (hq : 0 ≤ supportQ gD f s)
    (hdom : ∀ t ∈ Icc 0 (Real.pi / 2),
      g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t)) :
    sweptNiche U (Real.pi / 2) (secondTangentPoint g gD s).1 =
      (secondTangentPoint g gD s).2 := by
  refine sweptNiche_eq_of_global_contact hU hF hG ?_
    (fun t ht => .inr (hdom t (Ioo_subset_Icc_self ht))) hs ?_ ?_
  · simpa [hGtop, coordDot, companionNormal] using hdom 0 ⟨le_rfl, by positivity⟩
  · rw [secondTangentPoint, Reference.coordDot_companionSupportPoint]
    simp [Reference.supportProjection]
    linarith [show 0 ≤ gD s + f s - 1 from hq]
  · rw [secondTangentPoint, companionNormal_eq_unitNormal, Reference.coordDot_companionSupportPoint,
      add_sub_cancel_right, Reference.supportProjection_self]

/-- The standard corner is exposed globally by the later first walls and
the earlier companion walls. Its graph is traversed in reverse when its
horizontal coordinate decreases; the integration layer retains that sign. -/
theorem sweptNiche_innerCorner {U : Set Plane} (hU : IsCompact U)
    {f g fD gD : ℝ → ℝ}
    (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hFtop : f (Real.pi / 2) = 1) {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2))
    (hp : supportP fD g s ≤ 0) (hq : 0 ≤ supportQ gD f s)
    (hB : ∀ t ∈ Icc 0 (Real.pi / 2),
      f t - 1 ≤ coordDot (firstTangentPoint f fD s) (unitNormal t))
    (hD : ∀ t ∈ Icc 0 (Real.pi / 2),
      g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t)) :
    sweptNiche U (Real.pi / 2) (innerCornerPoint f g s).1 = (innerCornerPoint f g s).2 := by
  refine sweptNiche_eq_of_global_contact hU hF hG ?_ (fun t ht => ?_) hs ?_ ?_
  · have := hB _ ⟨by positivity, le_rfl⟩
    simp [hFtop, coordDot, unitNormal] at this
    rw [innerCorner_snd_eq_firstTangent f g fD]
    nlinarith [(sin_cos_pos_of_mem_quarter hs).2]
  · rcases le_total s t with hst | hts
    · refine .inl ?_
      rw [innerCorner_dot_eq_firstTangent f g fD]
      nlinarith [hB t (Ioo_subset_Icc_self ht), Real.sin_nonneg_of_nonneg_of_le_pi
        (sub_nonneg.mpr hst) (by linarith [ht.2, hs.1, Real.pi_pos])]
    · refine .inr ?_
      rw [innerCorner_dot_eq_secondTangent f g gD]
      nlinarith [hD t (Ioo_subset_Icc_self ht), Real.sin_nonneg_of_nonneg_of_le_pi
        (sub_nonneg.mpr hts) (by linarith [hs.2, ht.1, Real.pi_pos])]
  · refine le_of_eq ?_
    simp only [coordDot, innerCornerPoint, unitNormal]
    linear_combination (f s - 1) * Real.sin_sq_add_cos_sq s
  · refine le_of_eq ?_
    simp only [coordDot, innerCornerPoint, companionNormal]
    linear_combination (g s - 1) * Real.sin_sq_add_cos_sq s

end AmbidextrousSofa
