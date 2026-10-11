module

public import AmbidextrousSofa.Analysis.AngularFluxLimit

@[expose] public section

/-!
# Removing spatial endpoint cutoffs from the actual graph flux

Only the open portions of the visible graph pieces need positive height
and localized maximizing angles. Closed pieces cut off by `ε` and
continuity of the actual niche recover the endpoint chords as `ε → 0`.
A collapsed piece contributes zero, and the other piece is then split at
its midpoint.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.nicheGraphProjection_tendsto
    {U : Set Plane} (hU : IsDownwardCap U) {α : Type*} {f : Filter α} {l r : α → ℝ} {L R θ : ℝ}
    (hl : Tendsto l f (𝓝 L)) (hr : Tendsto r f (𝓝 R)) :
    Tendsto (fun n => nicheGraphProjection U θ (l n) (r n)) f
      (𝓝 (nicheGraphProjection U θ L R)) := by
  have hN {a : α → ℝ} {A : ℝ} (ha : Tendsto a f (𝓝 A)) :=
    (continuous_capSweptNiche.tendsto (hU.toCompactCap, A)).comp (tendsto_const_nhds.prodMk_nhds ha)
  exact ((hr.sub hl).const_mul _).add (((hN hr).sub (hN hl)).const_mul _)

open AngularGrid in
/-- Open visible pieces suffice, including collapsed ones. Every retained
cutoff lies strictly inside the actual middle window, while its endpoint
chord tends to the given chord. -/
theorem IsFullCapMaximizer.nicheGraphProjection_add_le_curvature_of_open_pieces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t φ δ a b a' b' l₁ r₁ l₂ r₂ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hab : a ≤ b) (hregular : Icc a b ⊆ regularCurvatureDomain m)
    (hab' : a' ≤ b') (hregular' : Icc a' b' ⊆ regularCurvatureDomain m) (hδ : 0 ≤ δ)
    (hsource : ∀ (grid : Finset QuarterAngle) (j : SourceIndex grid),
      sourceQuarterAngle (fullAngle grid j) ∈ Ioo s t → fullAngle grid j ∈ Ioc a b ∨
        fullAngle grid j ∈ Ioc a' b' ∧ Real.sin (fullAngle grid j - φ) ≤ δ)
    (hL : horizontalLeft U + capWidth U / 4 ≤ l₁)
    (h₁ : l₁ ≤ r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂)
    (hR : r₂ ≤ horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂, ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x → u ∈ Ioo s t) :
    nicheGraphProjection U φ l₁ r₁ + nicheGraphProjection U φ l₂ r₂ ≤
      (upperCurvature U).real (Ioc a b) +
        δ * ((upperCurvature U).real (Ioc a b) + (upperCurvature U).real (Ioc a' b')) := by
  set M := (upperCurvature U).real (Ioc a b) +
    δ * ((upperCurvature U).real (Ioc a b) + (upperCurvature U).real (Ioc a' b'))
  -- Two strict open pieces: cut both by `ε` and let `ε → 0`.
  have key {a₁ b₁ a₂ b₂ : ℝ} (h0 : horizontalLeft U + capWidth U / 4 ≤ a₁) (h1 : a₁ < b₁)
      (hg : b₁ ≤ a₂) (h2 : a₂ < b₂) (h3 : b₂ ≤ horizontalRight U - capWidth U / 4)
      (hsub : Ioo a₁ b₁ ∪ Ioo a₂ b₂ ⊆ Ioo l₁ r₁ ∪ Ioo l₂ r₂) :
      nicheGraphProjection U φ a₁ b₁ + nicheGraphProjection U φ a₂ b₂ ≤ M := by
    have hin (x : ℝ) : Tendsto (x + ·) (𝓝[>] 0) (𝓝 x) :=
      ((continuous_const_add x).tendsto' 0 x (add_zero x)).mono_left nhdsWithin_le_nhds
    have hout (x : ℝ) : Tendsto (x - ·) (𝓝[>] 0) (𝓝 x) :=
      ((continuous_const.sub continuous_id).tendsto' 0 x (sub_zero x)).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ((hU.isCap.nicheGraphProjection_tendsto (hin a₁) (hout b₁)).add
      (hU.isCap.nicheGraphProjection_tendsto (hin a₂) (hout b₂))) ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos (sub_pos.2 h1)),
      Ioo_mem_nhdsGT (half_pos (sub_pos.2 h2))] with ε ⟨hε, hε₁⟩ ⟨_, hε₂⟩
    have hs := (union_subset_union (Icc_subset_Ioo (lt_add_of_pos_right a₁ hε)
      (sub_lt_self b₁ hε)) (Icc_subset_Ioo (lt_add_of_pos_right a₂ hε) (sub_lt_self b₂ hε))).trans
        hsub
    exact hU.nicheGraphProjection_add_le_curvature hheight haffine hab hregular hab' hregular' hδ
      hsource (h0.trans_lt (lt_add_of_pos_right a₁ hε)) (by linarith only [hε₁])
      ((sub_le_self b₁ hε.le).trans (hg.trans (le_add_of_nonneg_right hε.le)))
      (by linarith only [hε₂]) ((sub_lt_self b₂ hε).trans_le h3)
      (fun x hx => hpositive x (hs hx)) (fun x hx => hmaximizers x (hs hx))
  -- A collapsed piece contributes zero: split the other piece at its midpoint.
  have hzero (x : ℝ) : nicheGraphProjection U φ x x = 0 := by simp [nicheGraphProjection]
  have split {l r : ℝ} (h : l < r) (hl : horizontalLeft U + capWidth U / 4 ≤ l)
      (hr : r ≤ horizontalRight U - capWidth U / 4) (hsub : Ioo l r ⊆ Ioo l₁ r₁ ∪ Ioo l₂ r₂) :
      nicheGraphProjection U φ l r ≤ M := by
    have hm₁ := left_lt_add_div_two.mpr h
    have hm₂ := add_div_two_lt_right.mpr h
    have := key hl hm₁ le_rfl hm₂ hr
      ((union_subset (Ioo_subset_Ioo_right hm₂.le) (Ioo_subset_Ioo_left hm₁.le)).trans hsub)
    simp only [nicheGraphProjection] at this ⊢
    linarith only [this]
  rcases h₁.eq_or_lt with rfl | h₁ <;> rcases h₂.eq_or_lt with rfl | h₂
  · rw [hzero, hzero, add_zero]
    exact add_nonneg measureReal_nonneg (mul_nonneg hδ (by positivity))
  · rw [hzero, zero_add]
    exact split h₂ (hL.trans hgap) hR subset_union_right
  · rw [hzero, add_zero]
    exact split h₁ hL (hgap.trans hR) subset_union_left
  · exact key hL h₁ hgap h₂ hR subset_rfl

end AmbidextrousSofa
