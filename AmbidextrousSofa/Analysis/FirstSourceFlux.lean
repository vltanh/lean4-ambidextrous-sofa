module

public import AmbidextrousSofa.Analysis.OpenGraphFlux

@[expose] public section

/-!
# First-family flux of visible core and tangent pieces

The projection onto the increasing first-wall tangent isolates the
first-family source mass. Its transverse companion contribution is
bounded by the angular interval length times the actual total source
mass. Open spatial pieces suffice, including a collapsed first-tangency
piece. All measures and selected polygons in the comparison are the
literal ones belonging to the prescribed full maximum.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid

open FinitePolygon

theorem localized_quarter_first_source_projection (grid : Finset QuarterAngle)
    {s t θ : ℝ} (hθ : θ ∈ Icc s t) (j : SourceIndex grid)
    (hj : sourceQuarterAngle (fullAngle grid j) ∈ Ioo s t) :
    fullAngle grid j ∈ Ioc s t ∨
      (fullAngle grid j ∈ Ioc (s + Real.pi / 2) (t + Real.pi / 2) ∧
        Real.sin (fullAngle grid j - (θ - Real.pi / 2)) ≤ t - s) := by
  rw [sourceQuarterAngle_fullAngle] at hj
  cases j with
  | inl u => exact Or.inl ⟨hj.1, hj.2.le⟩
  | inr u =>
    right
    constructor
    · change s + Real.pi / 2 < (u.val : ℝ) + Real.pi / 2 ∧
        (u.val : ℝ) + Real.pi / 2 ≤ t + Real.pi / 2
      constructor <;> linarith [hj.1, hj.2]
    · have hangle : fullAngle grid (Sum.inr u) - (θ - Real.pi / 2) =
          (u.val : ℝ) - θ + Real.pi := by
        change (u.val : ℝ) + Real.pi / 2 - (θ - Real.pi / 2) = _
        ring
      rw [hangle, Real.sin_add_pi]
      exact (neg_le_abs _).trans (Real.abs_sin_le_abs.trans
        (abs_le.mpr ⟨by linarith [hj.1, hθ.2], by linarith [hj.2, hθ.1]⟩))

theorem firstGraphProjection_add_le_curvature_of_selected_sequence
    {target : Set Plane} {U : ℕ → Set Plane} {a b m c s t θ l₁ r₁ l₂ r₂ : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (hL : horizontalLeft target + capWidth target / 4 < l₁)
    (h₁ : l₁ ≤ r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂)
    (hR : r₂ < horizontalRight target - capWidth target / 4)
    (hpositive : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂, 0 < sweptNiche target (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂,
      ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hTarget.isCap.toCompactCap x u = sweptNiche target (Real.pi / 2) x →
          u ∈ Ioo s t) :
    nicheGraphProjection target (θ - Real.pi / 2) l₁ r₁ +
        nicheGraphProjection target (θ - Real.pi / 2) l₂ r₂ ≤
      (upperCurvature target).real (Ioc s t) +
        (t - s) * ((upperCurvature target).real (Ioc s t) +
          (upperCurvature target).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hbox := fun n => (hU n).inBox
  have hwidth : 0 ≤ capWidth target := by
    unfold capWidth
    exact sub_nonneg.mpr (horizontalLeft_le_horizontalRight
      hTarget.isCap.nonempty hTarget.isCap.isCompact)
  have hFbox : Icc l₁ r₁ ∪ Icc l₂ r₂ ⊆ Icc a b := by
    intro x hx
    rcases hx with hx | hx <;> constructor <;> linarith [hx.1, hx.2]
  have hF : IsCompact (Icc l₁ r₁ ∪ Icc l₂ r₂) := isCompact_Icc.union isCompact_Icc
  have hpos := eventually_finiteBarrier_pos_on_compact hHausdorff hcap hTarget.isCap hlevel
    hbox hF hFbox hpositive
  have hlocal := eventually_innerSources_in_open_of_maximizers hHausdorff hcap hTarget.isCap hlevel
    hbox hF hFbox isOpen_Ioo hmaximizers
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hw := (hHausdorff.capWidth_tendsto hcap hTarget.isCap).div_const 4
  have hLl : ∀ᶠ n in atTop, horizontalLeft (U n) + capWidth (U n) / 4 < l₁ :=
    (hl.add hw).eventually (isOpen_Iio.mem_nhds hL)
  have hrR : ∀ᶠ n in atTop, r₂ < horizontalRight (U n) - capWidth (U n) / 4 :=
    (hr.sub hw).eventually (isOpen_Ioi.mem_nhds hR)
  have hst : s ≤ t := hθ.1.trans hθ.2
  have hδ : 0 ≤ t - s := sub_nonneg.mpr hst
  have hfinite : ∀ᶠ n in atTop,
      finiteGraphProjection (U n) (dyadic (level n)) (θ - Real.pi / 2) l₁ r₁ +
        finiteGraphProjection (U n) (dyadic (level n)) (θ - Real.pi / 2) l₂ r₂ ≤
      innerAngularMass (U n) (dyadic (level n)) (Ioc s t) +
        (t - s) * (innerAngularMass (U n) (dyadic (level n)) (Ioc s t) +
          innerAngularMass (U n) (dyadic (level n))
            (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
    filter_upwards [hpos, hlocal, hLl, hrR] with n hnpos hnlocal hnL hnR
    have hbound := finiteGraphProjection_add_le_sources (U n) (dyadic (level n))
      hnL.le h₁ hgap h₂ hnR.le hδ
      (fun x hx => hnpos x (Or.inl (Ioc_subset_Icc_self hx)))
      (fun x hx => hnpos x (Or.inr (Ioc_subset_Icc_self hx)))
      (fun x hx j hj => localized_quarter_first_source_projection _ hθ j
        (hnlocal x (Or.inl (Ioc_subset_Icc_self hx)) j hj))
      (fun x hx j hj => localized_quarter_first_source_projection _ hθ j
        (hnlocal x (Or.inr (Ioc_subset_Icc_self hx)) j hj))
    have hm := innerAngularMassOn_union_le (U n) (dyadic (level n)) (Ioc s t)
      (Ioc (s + Real.pi / 2) (t + Real.pi / 2))
      (show horizontalLeft (U n) + capWidth (U n) / 4 ≤
        horizontalRight (U n) - capWidth (U n) / 4 by linarith)
    simp only [innerAngularMassOn_middle] at hbound hm
    exact hbound.trans (add_le_add_left (mul_le_mul_of_nonneg_left hm hδ) _)
  have hbase := innerAngularMass_Ioc_tendsto_of_canonical_maximum hTarget hheight haffine hTargetBox
    hU hHausdorff hlevel hc hrate hleft hright hst hregular
  have hcomp := innerAngularMass_Ioc_tendsto_of_canonical_maximum hTarget hheight haffine hTargetBox
    hU hHausdorff hlevel hc hrate hleft hright
    (by linarith : s + Real.pi / 2 ≤ t + Real.pi / 2) hshift
  have hg₁ := finiteGraphProjection_tendsto (θ := θ - Real.pi / 2)
    hHausdorff hcap hTarget.isCap hlevel hbox
    (hFbox (Or.inl (left_mem_Icc.mpr h₁))) (hFbox (Or.inl (right_mem_Icc.mpr h₁)))
  have hg₂ := finiteGraphProjection_tendsto (θ := θ - Real.pi / 2)
    hHausdorff hcap hTarget.isCap hlevel hbox
    (hFbox (Or.inr (left_mem_Icc.mpr h₂))) (hFbox (Or.inr (right_mem_Icc.mpr h₂)))
  exact le_of_tendsto_of_tendsto (hg₁.add hg₂)
    (hbase.add ((hbase.add hcomp).const_mul (t - s))) hfinite

end AngularGrid

theorem IsFullCapMaximizer.firstGraphProjection_add_le_curvature
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ l₁ r₁ l₂ r₂ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (hL : horizontalLeft U + capWidth U / 4 < l₁)
    (h₁ : l₁ ≤ r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂)
    (hR : r₂ < horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂,
      ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x →
          u ∈ Ioo s t) :
    nicheGraphProjection U (θ - Real.pi / 2) l₁ r₁ +
        nicheGraphProjection U (θ - Real.pi / 2) l₂ r₂ ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp only [a, b]; linarith
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro P hP
    have hx := hU.isCap.fst_mem_Icc hP
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hP⟩ <;> dsimp only [a, b] <;>
      linarith only [hx.1, hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hab hbox
  exact AngularGrid.firstGraphProjection_add_le_curvature_of_selected_sequence
    hU hheight haffine hbox hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id)
    (fun n => (hc n).le) hrate (by dsimp only [a]; linarith) (by dsimp only [b]; linarith)
    hθ hregular hshift hL h₁ hgap h₂ hR hpositive hmaximizers

theorem IsFullCapMaximizer.firstGraphProjection_le_curvature_of_open_piece
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
    nicheGraphProjection U (θ - Real.pi / 2) l r ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  let ε : ℕ → ℝ := fun n => AngularGrid.selectionRate n / 4
  let left : ℕ → ℝ := fun n => l + ε n * (r - l)
  let right : ℕ → ℝ := fun n => r - ε n * (r - l)
  have hcut (n : ℕ) : l < left n ∧ left n < right n ∧ right n < r :=
    fluxInset_interval hlr (fluxInset_bounds n).1 (fluxInset_bounds n).2
  have hbound (n : ℕ) : nicheGraphProjection U (θ - Real.pi / 2) (left n) (right n) ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
    have hsub : Icc (left n) (left n) ∪ Icc (left n) (right n) ⊆ Ioo l r := by
      intro x hx
      rcases hx with hx | hx <;>
        exact ⟨(hcut n).1.trans_le hx.1,
          hx.2.trans_lt (by linarith [(hcut n).2.1, (hcut n).2.2])⟩
    have h := hU.firstGraphProjection_add_le_curvature hheight haffine hθ hregular hshift
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
  exact le_of_tendsto (hU.isCap.nicheGraphProjection_tendsto (θ := θ - Real.pi / 2) hl hr)
    (Eventually.of_forall hbound)

/-- The core interval is strict; the charged tangent interval may
collapse. Both are projected in the same increasing first-wall direction. -/
theorem IsFullCapMaximizer.firstGraphProjection_add_le_curvature_of_open_pieces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ l₁ r₁ l₂ r₂ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (hL : horizontalLeft U + capWidth U / 4 ≤ l₁)
    (h₁ : l₁ < r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂)
    (hR : r₂ ≤ horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂,
      ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x → u ∈ Ioo s t) :
    nicheGraphProjection U (θ - Real.pi / 2) l₁ r₁ +
        nicheGraphProjection U (θ - Real.pi / 2) l₂ r₂ ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  rcases h₂.eq_or_lt with heq | h₂strict
  · subst r₂
    have h := hU.firstGraphProjection_le_curvature_of_open_piece hheight haffine hθ
      hregular hshift hL h₁ (hgap.trans hR)
      (fun x hx => hpositive x (Or.inl hx))
      (fun x hx u hu hmax => hmaximizers x (Or.inl hx) u hu hmax)
    simpa only [nicheGraphProjection, sub_self, mul_zero, add_zero] using h
  let ε : ℕ → ℝ := fun n => AngularGrid.selectionRate n / 4
  let left₁ : ℕ → ℝ := fun n => l₁ + ε n * (r₁ - l₁)
  let right₁ : ℕ → ℝ := fun n => r₁ - ε n * (r₁ - l₁)
  let left₂ : ℕ → ℝ := fun n => l₂ + ε n * (r₂ - l₂)
  let right₂ : ℕ → ℝ := fun n => r₂ - ε n * (r₂ - l₂)
  have hcut₁ (n : ℕ) : l₁ < left₁ n ∧ left₁ n < right₁ n ∧ right₁ n < r₁ :=
    fluxInset_interval h₁ (fluxInset_bounds n).1 (fluxInset_bounds n).2
  have hcut₂ (n : ℕ) : l₂ < left₂ n ∧ left₂ n < right₂ n ∧ right₂ n < r₂ :=
    fluxInset_interval h₂strict (fluxInset_bounds n).1 (fluxInset_bounds n).2
  have hbound (n : ℕ) :
      nicheGraphProjection U (θ - Real.pi / 2) (left₁ n) (right₁ n) +
        nicheGraphProjection U (θ - Real.pi / 2) (left₂ n) (right₂ n) ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
    have hsub : Icc (left₁ n) (right₁ n) ∪ Icc (left₂ n) (right₂ n) ⊆
        Ioo l₁ r₁ ∪ Ioo l₂ r₂ := by
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl ⟨(hcut₁ n).1.trans_le hx.1, hx.2.trans_lt (hcut₁ n).2.2⟩
      · exact Or.inr ⟨(hcut₂ n).1.trans_le hx.1, hx.2.trans_lt (hcut₂ n).2.2⟩
    exact hU.firstGraphProjection_add_le_curvature hheight haffine hθ hregular hshift
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
  exact le_of_tendsto ((hU.isCap.nicheGraphProjection_tendsto
    (θ := θ - Real.pi / 2) hl₁ hr₁).add (hU.isCap.nicheGraphProjection_tendsto
      (θ := θ - Real.pi / 2) hl₂ hr₂)) (Eventually.of_forall hbound)

/-- A literal visible core chord. Every maximizing angle over its open
spatial projection lies in the stated parameter interval. -/
structure FirstSourceCorePiece {U : Set Plane} (hU : IsDownwardCap U)
    (Z : ℝ → Plane) (s t : ℝ) : Prop where
  reversed : (Z t).1 < (Z s).1
  middle_left : horizontalLeft U + capWidth U / 4 ≤ (Z t).1
  middle_right : (Z s).1 ≤ horizontalRight U - capWidth U / 4
  contact_s : sweptNiche U (Real.pi / 2) (Z s).1 = (Z s).2
  contact_t : sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2
  positive : ∀ x ∈ Ioo (Z t).1 (Z s).1, 0 < sweptNiche U (Real.pi / 2) x
  localizes : ∀ x ∈ Ioo (Z t).1 (Z s).1, ∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip hU.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t

/-- Two disjoint literal graph pieces. The first tangent may be a
plateau; its zero projection is then retained exactly. -/
structure FirstSourceChargedPieces {U : Set Plane} (hU : IsDownwardCap U)
    (B Z : ℝ → Plane) (s t : ℝ) : Prop where
  core : FirstSourceCorePiece hU Z s t
  tangent_order : (B s).1 ≤ (B t).1
  separation : (Z s).1 ≤ (B s).1
  middle_right : (B t).1 ≤ horizontalRight U - capWidth U / 4
  contact_s : sweptNiche U (Real.pi / 2) (B s).1 = (B s).2
  contact_t : sweptNiche U (Real.pi / 2) (B t).1 = (B t).2
  positive : ∀ x ∈ Ioo (B s).1 (B t).1, 0 < sweptNiche U (Real.pi / 2) x
  localizes : ∀ x ∈ Ioo (B s).1 (B t).1, ∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip hU.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t

theorem IsFullCapMaximizer.first_source_flux_of_core_piece
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ : ℝ} {Z : ℝ → Plane}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (H : FirstSourceCorePiece hU.isCap Z s t) :
    Real.sin θ * ((Z s).1 - (Z t).1) - Real.cos θ * ((Z s).2 - (Z t).2) ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  have h := hU.firstGraphProjection_le_curvature_of_open_piece hheight haffine hθ
    hregular hshift H.middle_left H.reversed H.middle_right H.positive H.localizes
  convert h using 1 <;>
    simp only [nicheGraphProjection, H.contact_s, H.contact_t, Real.cos_sub, Real.sin_sub,
      Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add, zero_sub] <;> ring

theorem IsFullCapMaximizer.first_source_flux_of_charged_pieces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ : ℝ} {B Z : ℝ → Plane}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (H : FirstSourceChargedPieces hU.isCap B Z s t) :
    Real.sin θ * ((Z s).1 - (Z t).1) - Real.cos θ * ((Z s).2 - (Z t).2) +
      (Real.sin θ * ((B t).1 - (B s).1) - Real.cos θ * ((B t).2 - (B s).2)) ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  have h := hU.firstGraphProjection_add_le_curvature_of_open_pieces hheight haffine hθ
    hregular hshift H.core.middle_left H.core.reversed H.separation H.tangent_order H.middle_right
    (fun x hx => by
      rcases hx with hx | hx
      · exact H.core.positive x hx
      · exact H.positive x hx)
    (fun x hx v hv hmax => by
      rcases hx with hx | hx
      · exact H.core.localizes x hx v hv hmax
      · exact H.localizes x hx v hv hmax)
  convert h using 1 <;>
    simp only [nicheGraphProjection, H.core.contact_s, H.core.contact_t,
      H.contact_s, H.contact_t, Real.cos_sub, Real.sin_sub, Real.cos_pi_div_two,
      Real.sin_pi_div_two, mul_zero, mul_one, zero_add, zero_sub] <;> ring

end AmbidextrousSofa
