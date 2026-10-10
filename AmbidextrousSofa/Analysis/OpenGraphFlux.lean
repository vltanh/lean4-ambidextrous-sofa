module

public import AmbidextrousSofa.Analysis.AngularFluxLimit

@[expose] public section

/-!
# Removing spatial endpoint cutoffs from the actual graph flux

Only the open portions of a visible graph piece need positive height and
localized maximizing angles. Linear interior cutoffs and continuity of
the actual niche recover the closed endpoint chord. A degenerate first
piece contributes zero and is treated by the one-piece bound.
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
  have hNl := (continuous_capSweptNiche.tendsto (hU.toCompactCap, L)).comp
    (tendsto_const_nhds.prodMk_nhds hl)
  have hNr := (continuous_capSweptNiche.tendsto (hU.toCompactCap, R)).comp
    (tendsto_const_nhds.prodMk_nhds hr)
  exact ((hr.sub hl).const_mul (Real.cos θ)).add
    ((hNr.sub hNl).const_mul (Real.sin θ))

theorem fluxInset_bounds (n : ℕ) :
    0 < AngularGrid.selectionRate n / 4 ∧ AngularGrid.selectionRate n / 4 < 1 / 2 := by
  have hpos := AngularGrid.selectionRate_pos n
  have hle : AngularGrid.selectionRate n ≤ 1 := by
    unfold AngularGrid.selectionRate
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  constructor <;> linarith

theorem fluxInset_interval {l r ε : ℝ} (hlr : l < r) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    l < l + ε * (r - l) ∧
      l + ε * (r - l) < r - ε * (r - l) ∧
        r - ε * (r - l) < r := by
  have hmul := mul_pos hε0 (sub_pos.mpr hlr)
  have hwidth := mul_pos (by linarith : 0 < 1 - 2 * ε) (sub_pos.mpr hlr)
  constructor
  · linarith
  constructor <;> nlinarith

theorem IsFullCapMaximizer.nicheGraphProjection_le_curvature_of_open_piece
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ l r : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (hL : horizontalLeft U + capWidth U / 4 ≤ l) (hlr : l < r)
    (hR : r ≤ horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Ioo l r, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Ioo l r, ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x → u ∈ Ioo s t) :
    nicheGraphProjection U θ l r ≤
      (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * ((upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (upperCurvature U).real (Ioc s t)) := by
  let ε : ℕ → ℝ := fun n => AngularGrid.selectionRate n / 4
  let left : ℕ → ℝ := fun n => l + ε n * (r - l)
  let right : ℕ → ℝ := fun n => r - ε n * (r - l)
  have hcut (n : ℕ) : l < left n ∧ left n < right n ∧ right n < r :=
    fluxInset_interval hlr (fluxInset_bounds n).1 (fluxInset_bounds n).2
  have hbound (n : ℕ) : nicheGraphProjection U θ (left n) (right n) ≤
      (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * ((upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (upperCurvature U).real (Ioc s t)) := by
    have hsub : Icc (left n) (left n) ∪ Icc (left n) (right n) ⊆ Ioo l r := by
      intro x hx
      rcases hx with hx | hx <;>
        exact ⟨(hcut n).1.trans_le hx.1,
          hx.2.trans_lt (by linarith [(hcut n).2.1, (hcut n).2.2])⟩
    have h := hU.nicheGraphProjection_add_le_curvature hheight haffine hθ hregular hshift
      (hL.trans_lt (hcut n).1) le_rfl le_rfl (hcut n).2.1.le
      ((hcut n).2.2.trans_le hR)
      (fun x hx => hpositive x (hsub hx))
      (fun x hx u hu hmax => hmaximizers x (hsub hx) u hu hmax)
    simpa only [nicheGraphProjection, sub_self, mul_zero, add_zero, zero_add] using h
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [zero_div] using AngularGrid.selectionRate_tendsto.div_const 4
  have hl : Tendsto left atTop (𝓝 l) := by
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hε.mul_const (r - l))
  have hr : Tendsto right atTop (𝓝 r) := by
    simpa only [zero_mul, sub_zero] using tendsto_const_nhds.sub (hε.mul_const (r - l))
  exact le_of_tendsto (hU.isCap.nicheGraphProjection_tendsto (θ := θ) hl hr)
    (Eventually.of_forall hbound)

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
  rcases h₁.eq_or_lt with heq | h₁strict
  · subst r₁
    have h := hU.nicheGraphProjection_le_curvature_of_open_piece hheight haffine hθ
      hregular hshift (hL.trans hgap) h₂ hR
      (fun x hx => hpositive x (Or.inr hx))
      (fun x hx u hu hmax => hmaximizers x (Or.inr hx) u hu hmax)
    simpa only [nicheGraphProjection, sub_self, mul_zero, add_zero, zero_add] using h
  let ε : ℕ → ℝ := fun n => AngularGrid.selectionRate n / 4
  let left₁ : ℕ → ℝ := fun n => l₁ + ε n * (r₁ - l₁)
  let right₁ : ℕ → ℝ := fun n => r₁ - ε n * (r₁ - l₁)
  let left₂ : ℕ → ℝ := fun n => l₂ + ε n * (r₂ - l₂)
  let right₂ : ℕ → ℝ := fun n => r₂ - ε n * (r₂ - l₂)
  have hcut₁ (n : ℕ) : l₁ < left₁ n ∧ left₁ n < right₁ n ∧ right₁ n < r₁ :=
    fluxInset_interval h₁strict (fluxInset_bounds n).1 (fluxInset_bounds n).2
  have hcut₂ (n : ℕ) : l₂ < left₂ n ∧ left₂ n < right₂ n ∧ right₂ n < r₂ :=
    fluxInset_interval h₂ (fluxInset_bounds n).1 (fluxInset_bounds n).2
  have hbound (n : ℕ) :
      nicheGraphProjection U θ (left₁ n) (right₁ n) + nicheGraphProjection U θ (left₂ n) (right₂ n) ≤
      (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * ((upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (upperCurvature U).real (Ioc s t)) := by
    have hsub : Icc (left₁ n) (right₁ n) ∪ Icc (left₂ n) (right₂ n) ⊆
        Ioo l₁ r₁ ∪ Ioo l₂ r₂ := by
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl ⟨(hcut₁ n).1.trans_le hx.1, hx.2.trans_lt (hcut₁ n).2.2⟩
      · exact Or.inr ⟨(hcut₂ n).1.trans_le hx.1, hx.2.trans_lt (hcut₂ n).2.2⟩
    exact hU.nicheGraphProjection_add_le_curvature hheight haffine hθ hregular hshift
      (hL.trans_lt (hcut₁ n).1) (hcut₁ n).2.1.le
      ((hcut₁ n).2.2.le.trans (hgap.trans (hcut₂ n).1.le)) (hcut₂ n).2.1.le
      ((hcut₂ n).2.2.trans_le hR)
      (fun x hx => hpositive x (hsub hx))
      (fun x hx u hu hmax => hmaximizers x (hsub hx) u hu hmax)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [zero_div] using AngularGrid.selectionRate_tendsto.div_const 4
  have hl₁ : Tendsto left₁ atTop (𝓝 l₁) := by
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hε.mul_const (r₁ - l₁))
  have hr₁ : Tendsto right₁ atTop (𝓝 r₁) := by
    simpa only [zero_mul, sub_zero] using tendsto_const_nhds.sub (hε.mul_const (r₁ - l₁))
  have hl₂ : Tendsto left₂ atTop (𝓝 l₂) := by
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hε.mul_const (r₂ - l₂))
  have hr₂ : Tendsto right₂ atTop (𝓝 r₂) := by
    simpa only [zero_mul, sub_zero] using tendsto_const_nhds.sub (hε.mul_const (r₂ - l₂))
  exact le_of_tendsto ((hU.isCap.nicheGraphProjection_tendsto (θ := θ) hl₁ hr₁).add
    (hU.isCap.nicheGraphProjection_tendsto (θ := θ) hl₂ hr₂)) (Eventually.of_forall hbound)

end AmbidextrousSofa
