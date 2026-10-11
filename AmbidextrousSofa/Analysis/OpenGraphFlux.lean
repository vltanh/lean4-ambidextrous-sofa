module

public import AmbidextrousSofa.Analysis.AngularFluxLimit

@[expose] public section

/-!
# Removing spatial endpoint cutoffs from the actual graph flux

Only the open portions of a visible graph piece need positive height and
localized maximizing angles. Linear interior cutoffs and continuity of
the actual niche recover the closed endpoint chord. A degenerate first
piece contributes zero and is treated by splitting the second piece.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.nicheGraphProjection_tendsto
    {U : Set Plane} (hU : IsDownwardCap U) {l r : ℕ → ℝ} {L R θ : ℝ}
    (hl : Tendsto l atTop (𝓝 L)) (hr : Tendsto r atTop (𝓝 R)) :
    Tendsto (fun n => nicheGraphProjection U θ (l n) (r n)) atTop
      (𝓝 (nicheGraphProjection U θ L R)) := by
  have hN {a : ℕ → ℝ} {A : ℝ} (ha : Tendsto a atTop (𝓝 A)) :=
    (continuous_capSweptNiche.tendsto (hU.toCompactCap, A)).comp (tendsto_const_nhds.prodMk_nhds ha)
  exact ((hr.sub hl).const_mul _).add (((hN hr).sub (hN hl)).const_mul _)

theorem fluxInset_bounds (n : ℕ) :
    0 < AngularGrid.selectionRate n / 4 ∧ AngularGrid.selectionRate n / 4 < 1 / 2 := by
  have : AngularGrid.selectionRate n ≤ 1 := div_le_one_of_le₀ (by simp) (by positivity)
  exact ⟨by linarith [AngularGrid.selectionRate_pos n], by linarith⟩

theorem fluxInset_interval {l r ε : ℝ} (hlr : l < r) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    l < l + ε * (r - l) ∧
      l + ε * (r - l) < r - ε * (r - l) ∧
        r - ε * (r - l) < r := by
  have := mul_pos hε0 (sub_pos.mpr hlr)
  have := mul_pos (by linarith : 0 < 1 - 2 * ε) (sub_pos.mpr hlr)
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Open visible pieces suffice, including a collapsed first tangency
piece. Every retained cutoff lies strictly inside the actual middle
window, while its endpoint chord tends to the desired physical chord. -/
theorem IsFullCapMaximizer.nicheGraphProjection_add_le_curvature_of_open_pieces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ l₁ r₁ l₂ r₂ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (hL : horizontalLeft U + capWidth U / 4 ≤ l₁)
    (h₁ : l₁ ≤ r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ < r₂)
    (hR : r₂ ≤ horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂,
      ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x → u ∈ Ioo s t) :
    nicheGraphProjection U θ l₁ r₁ + nicheGraphProjection U θ l₂ r₂ ≤
      (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * ((upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (upperCurvature U).real (Ioc s t)) := by
  have hε : Tendsto (fun n => AngularGrid.selectionRate n / 4) atTop (𝓝 0) := by
    simpa only [zero_div] using AngularGrid.selectionRate_tendsto.div_const 4
  -- Two open pieces inside the given ones: cut both by the inset `selectionRate n / 4`.
  have key {a₁ b₁ a₂ b₂ : ℝ} (h0 : horizontalLeft U + capWidth U / 4 ≤ a₁) (h1 : a₁ < b₁)
      (hg : b₁ ≤ a₂) (h2 : a₂ < b₂) (h3 : b₂ ≤ horizontalRight U - capWidth U / 4)
      (hsub : Ioo a₁ b₁ ∪ Ioo a₂ b₂ ⊆ Ioo l₁ r₁ ∪ Ioo l₂ r₂) :
      nicheGraphProjection U θ a₁ b₁ + nicheGraphProjection U θ a₂ b₂ ≤
        (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (t - s) * ((upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
            (upperCurvature U).real (Ioc s t)) := by
    have hin (a b : ℝ) := (tendsto_const_nhds (x := a)).add (hε.mul_const (b - a))
    have hout (a b : ℝ) := (tendsto_const_nhds (x := b)).sub (hε.mul_const (b - a))
    simp only [zero_mul, add_zero, sub_zero] at hin hout
    refine le_of_tendsto ((hU.isCap.nicheGraphProjection_tendsto (hin a₁ b₁) (hout a₁ b₁)).add
      (hU.isCap.nicheGraphProjection_tendsto (hin a₂ b₂) (hout a₂ b₂)))
      (Eventually.of_forall fun n => ?_)
    obtain ⟨c1, c2, c3⟩ := fluxInset_interval h1 (fluxInset_bounds n).1 (fluxInset_bounds n).2
    obtain ⟨d1, d2, d3⟩ := fluxInset_interval h2 (fluxInset_bounds n).1 (fluxInset_bounds n).2
    have hs := (union_subset_union (Icc_subset_Ioo c1 c3) (Icc_subset_Ioo d1 d3)).trans hsub
    exact hU.nicheGraphProjection_add_le_curvature hheight haffine hθ hregular hshift
      (h0.trans_lt c1) c2.le (c3.le.trans (hg.trans d1.le)) d2.le (d3.trans_le h3)
      (fun x hx => hpositive x (hs hx)) (fun x hx => hmaximizers x (hs hx))
  rcases h₁.eq_or_lt with rfl | h₁
  · -- A degenerate first piece: split the second one at its midpoint instead.
    obtain ⟨hm₁, hm₂⟩ : l₂ < (l₂ + r₂) / 2 ∧ (l₂ + r₂) / 2 < r₂ := ⟨by linarith, by linarith⟩
    have := key (hL.trans hgap) hm₁ le_rfl hm₂ hR fun x hx =>
      .inr (hx.elim (fun h => ⟨h.1, h.2.trans hm₂⟩) fun h => ⟨hm₁.trans h.1, h.2⟩)
    simp only [nicheGraphProjection] at this ⊢
    linarith
  · exact key hL h₁ hgap h₂ hR subset_rfl

end AmbidextrousSofa
