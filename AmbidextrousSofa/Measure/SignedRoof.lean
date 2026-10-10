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
  have h := Reference.supportProjection_le_self
    (continuous_const.sub hf) hfD.neg
    (fun x => by simpa only [zero_sub] using
      (hasDerivWithinAt_const (x := x) (s := Ioi x) (c := (1 : ℝ))).sub (hderiv x))
    (fun x => (hsecond x).neg)
    (hDD := fun x => -fDD x)
    (by intro x hx; dsimp; linarith [hcurv x hx])
    (by linarith [Real.pi_pos]) hs ht
  unfold firstTangentPoint
  rw [Reference.coordDot_supportPoint]
  unfold Reference.supportProjection at h ⊢
  dsimp at h
  nlinarith

theorem secondTangent_dominates_support {g gD gDD : ℝ → ℝ}
    (hg : Continuous g) (hgD : Continuous gD)
    (hderiv : ∀ t, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecond : ∀ t, HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hcurv : ∀ t ∈ Icc 0 (Real.pi / 2), g t + gDD t ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t) := by
  have h := Reference.supportProjection_le_self
    (continuous_const.sub hg) hgD.neg
    (fun x => by simpa only [zero_sub] using
      (hasDerivWithinAt_const (x := x) (s := Ioi x) (c := (1 : ℝ))).sub (hderiv x))
    (fun x => (hsecond x).neg)
    (hDD := fun x => -gDD x)
    (by intro x hx; dsimp; linarith [hcurv x hx])
    (by linarith [Real.pi_pos]) hs ht
  unfold secondTangentPoint
  rw [companionNormal_eq_unitNormal, Reference.coordDot_companionSupportPoint,
    add_sub_cancel_right]
  unfold Reference.supportProjection at h ⊢
  dsimp at h
  nlinarith

theorem coordDot_firstTangent_unit (f fD : ℝ → ℝ) (t : ℝ) :
    coordDot (firstTangentPoint f fD t) (unitNormal t) = f t - 1 := by
  unfold firstTangentPoint
  rw [Reference.coordDot_supportPoint, Reference.supportProjection_self]

theorem coordDot_firstTangent_companion (f fD : ℝ → ℝ) (t : ℝ) :
    coordDot (firstTangentPoint f fD t) (companionNormal t) = fD t := by
  unfold firstTangentPoint
  rw [companionNormal_eq_unitNormal, Reference.coordDot_supportPoint]
  simp [Reference.supportProjection, add_sub_cancel_left]

theorem coordDot_secondTangent_unit (g gD : ℝ → ℝ) (t : ℝ) :
    coordDot (secondTangentPoint g gD t) (unitNormal t) = -gD t := by
  unfold secondTangentPoint
  rw [Reference.coordDot_companionSupportPoint]
  have hangle : t - Real.pi / 2 - t = -(Real.pi / 2) := by ring
  simp [Reference.supportProjection, hangle]

theorem coordDot_secondTangent_companion (g gD : ℝ → ℝ) (t : ℝ) :
    coordDot (secondTangentPoint g gD t) (companionNormal t) = g t - 1 := by
  unfold secondTangentPoint
  rw [companionNormal_eq_unitNormal, Reference.coordDot_companionSupportPoint,
    add_sub_cancel_right, Reference.supportProjection_self]

theorem coordDot_innerCorner_unit (f g : ℝ → ℝ) (t : ℝ) :
    coordDot (innerCornerPoint f g t) (unitNormal t) = f t - 1 := by
  calc
    _ = (f t - 1) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by
      unfold coordDot innerCornerPoint unitNormal
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem coordDot_innerCorner_companion (f g : ℝ → ℝ) (t : ℝ) :
    coordDot (innerCornerPoint f g t) (companionNormal t) = g t - 1 := by
  calc
    _ = (g t - 1) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by
      unfold coordDot innerCornerPoint companionNormal
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

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
  unfold secondTangentPoint
  rw [companionSupportPoint_coordinates]
  unfold coordDot innerCornerPoint companionNormal supportQ
  rw [Real.sin_sub]
  ring

theorem innerCorner_snd_eq_firstTangent (f g fD : ℝ → ℝ) (s : ℝ) :
    (innerCornerPoint f g s).2 = (firstTangentPoint f fD s).2 -
      supportP fD g s * Real.cos s := by
  unfold innerCornerPoint firstTangentPoint Reference.supportPoint supportP
  ring

theorem firstTangent_snd_nonneg {f fD : ℝ → ℝ} {s : ℝ}
    (htop : f (Real.pi / 2) = 1)
    (hdom : ∀ t ∈ Icc 0 (Real.pi / 2),
      f t - 1 ≤ coordDot (firstTangentPoint f fD s) (unitNormal t)) :
    0 ≤ (firstTangentPoint f fD s).2 := by
  have h := hdom (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩
  simpa only [htop, sub_self, coordDot, unitNormal, Real.cos_pi_div_two,
    Real.sin_pi_div_two, mul_zero, mul_one, zero_add] using h

theorem secondTangent_snd_nonneg {g gD : ℝ → ℝ} {s : ℝ}
    (htop : g 0 = 1)
    (hdom : ∀ t ∈ Icc 0 (Real.pi / 2),
      g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t)) :
    0 ≤ (secondTangentPoint g gD s).2 := by
  have h := hdom 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
  simpa only [htop, sub_self, coordDot, companionNormal, Real.sin_zero,
    Real.cos_zero, neg_zero, mul_zero, mul_one, zero_add] using h

theorem firstWall_le_of_support_depth {U : Set Plane} {θ : ℝ} {p : Plane}
    (hs : 0 < Real.sin θ) (h : support U (unitNormal θ) - 1 ≤ coordDot p (unitNormal θ)) :
    firstWall U θ p.1 ≤ p.2 := by
  unfold firstWall
  apply (div_le_iff₀ hs).mpr
  unfold coordDot unitNormal at h
  nlinarith

theorem secondWall_le_of_support_depth {U : Set Plane} {θ : ℝ} {p : Plane}
    (hc : 0 < Real.cos θ)
    (h : support U (companionNormal θ) - 1 ≤ coordDot p (companionNormal θ)) :
    secondWall U θ p.1 ≤ p.2 := by
  unfold secondWall
  apply (div_le_iff₀ hc).mpr
  unfold coordDot companionNormal at h
  nlinarith

theorem le_firstWall_of_support_depth {U : Set Plane} {θ : ℝ} {p : Plane}
    (hs : 0 < Real.sin θ) (h : coordDot p (unitNormal θ) ≤ support U (unitNormal θ) - 1) :
    p.2 ≤ firstWall U θ p.1 := by
  unfold firstWall
  apply (le_div_iff₀ hs).mpr
  unfold coordDot unitNormal at h
  nlinarith

theorem le_secondWall_of_support_depth {U : Set Plane} {θ : ℝ} {p : Plane}
    (hc : 0 < Real.cos θ)
    (h : coordDot p (companionNormal θ) ≤ support U (companionNormal θ) - 1) :
    p.2 ≤ secondWall U θ p.1 := by
  unfold secondWall
  apply (le_div_iff₀ hc).mpr
  unfold coordDot companionNormal at h
  nlinarith

theorem firstWall_eq_of_support_depth {U : Set Plane} {θ : ℝ} {p : Plane}
    (hs : 0 < Real.sin θ) (h : support U (unitNormal θ) - 1 = coordDot p (unitNormal θ)) :
    firstWall U θ p.1 = p.2 :=
  le_antisymm (firstWall_le_of_support_depth hs h.le)
    (le_firstWall_of_support_depth hs h.symm.le)

theorem secondWall_eq_of_support_depth {U : Set Plane} {θ : ℝ} {p : Plane}
    (hc : 0 < Real.cos θ)
    (h : support U (companionNormal θ) - 1 = coordDot p (companionNormal θ)) :
    secondWall U θ p.1 = p.2 :=
  le_antisymm (secondWall_le_of_support_depth hc h.le)
    (le_secondWall_of_support_depth hc h.symm.le)

theorem sweptNiche_eq_of_global_contact {U : Set Plane} (hU : IsCompact U)
    {p : Plane} (hp : 0 ≤ p.2)
    (hbound : ∀ t ∈ Ioo 0 (Real.pi / 2), cornerWall U t p.1 ≤ p.2)
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2)) (hcontact : cornerWall U s p.1 = p.2) :
    sweptNiche U (Real.pi / 2) p.1 = p.2 := by
  apply le_antisymm (sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hp hbound)
  rw [← hcontact]
  exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU le_rfl p.1) hs

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
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1
    (by linarith [hs.2, Real.pi_pos])
  have hcos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
  apply sweptNiche_eq_of_global_contact hU (firstTangent_snd_nonneg hFtop hdom) ?_ hs
  · intro t ht
    apply (min_le_left _ _).trans
    apply firstWall_le_of_support_depth (Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2, Real.pi_pos]))
    rw [hF t ⟨ht.1.le, ht.2.le⟩]
    exact hdom t ⟨ht.1.le, ht.2.le⟩
  · have hfirst := firstWall_eq_of_support_depth hsin (p := firstTangentPoint f fD s)
      (by rw [hF s ⟨hs.1.le, hs.2.le⟩, coordDot_firstTangent_unit])
    have hsecond := le_secondWall_of_support_depth hcos (p := firstTangentPoint f fD s)
      (by rw [hG s ⟨hs.1.le, hs.2.le⟩, coordDot_firstTangent_companion];
          unfold supportP at hp; linarith)
    unfold cornerWall
    rw [hfirst, min_eq_left hsecond]

theorem sweptNiche_secondTangent {U : Set Plane} (hU : IsCompact U)
    {f g gD : ℝ → ℝ} (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hGtop : g 0 = 1) {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2))
    (hq : 0 ≤ supportQ gD f s)
    (hdom : ∀ t ∈ Icc 0 (Real.pi / 2),
      g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t)) :
    sweptNiche U (Real.pi / 2) (secondTangentPoint g gD s).1 =
      (secondTangentPoint g gD s).2 := by
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1
    (by linarith [hs.2, Real.pi_pos])
  have hcos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
  apply sweptNiche_eq_of_global_contact hU (secondTangent_snd_nonneg hGtop hdom) ?_ hs
  · intro t ht
    apply (min_le_right _ _).trans
    apply secondWall_le_of_support_depth (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    rw [hG t ⟨ht.1.le, ht.2.le⟩]
    exact hdom t ⟨ht.1.le, ht.2.le⟩
  · have hsecond := secondWall_eq_of_support_depth hcos (p := secondTangentPoint g gD s)
      (by rw [hG s ⟨hs.1.le, hs.2.le⟩, coordDot_secondTangent_companion])
    have hfirst := le_firstWall_of_support_depth hsin (p := secondTangentPoint g gD s)
      (by rw [hF s ⟨hs.1.le, hs.2.le⟩, coordDot_secondTangent_unit];
          unfold supportQ at hq; linarith)
    unfold cornerWall
    rw [hsecond, min_eq_right hfirst]

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
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1
    (by linarith [hs.2, Real.pi_pos])
  have hcos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
  have hy : 0 ≤ (innerCornerPoint f g s).2 := by
    rw [innerCorner_snd_eq_firstTangent f g fD]
    exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hp hcos.le).trans
      (firstTangent_snd_nonneg hFtop hB))
  apply sweptNiche_eq_of_global_contact hU hy ?_ hs
  · intro t ht
    rcases le_total s t with hst | hts
    · apply (min_le_left _ _).trans
      apply firstWall_le_of_support_depth (Real.sin_pos_of_pos_of_lt_pi ht.1
        (by linarith [ht.2, Real.pi_pos]))
      rw [hF t ⟨ht.1.le, ht.2.le⟩, innerCorner_dot_eq_firstTangent f g fD]
      have htrig : 0 ≤ Real.sin (t - s) := Real.sin_nonneg_of_nonneg_of_le_pi
        (sub_nonneg.mpr hst) (by linarith [ht.2, hs.1, Real.pi_pos])
      have hprod := mul_nonpos_of_nonpos_of_nonneg hp htrig
      have hb := hB t ⟨ht.1.le, ht.2.le⟩
      linarith
    · apply (min_le_right _ _).trans
      apply secondWall_le_of_support_depth (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      rw [hG t ⟨ht.1.le, ht.2.le⟩, innerCorner_dot_eq_secondTangent f g gD]
      have htrig : 0 ≤ Real.sin (s - t) := Real.sin_nonneg_of_nonneg_of_le_pi
        (sub_nonneg.mpr hts) (by linarith [hs.2, ht.1, Real.pi_pos])
      exact (hD t ⟨ht.1.le, ht.2.le⟩).trans (le_add_of_nonneg_right (mul_nonneg hq htrig))
  · have hfirst := firstWall_eq_of_support_depth hsin (p := innerCornerPoint f g s)
      (by rw [hF s ⟨hs.1.le, hs.2.le⟩, coordDot_innerCorner_unit])
    have hsecond := secondWall_eq_of_support_depth hcos (p := innerCornerPoint f g s)
      (by rw [hG s ⟨hs.1.le, hs.2.le⟩, coordDot_innerCorner_companion])
    simp only [cornerWall, hfirst, hsecond, min_self]

end AmbidextrousSofa
