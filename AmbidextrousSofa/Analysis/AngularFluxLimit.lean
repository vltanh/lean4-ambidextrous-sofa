import AmbidextrousSofa.Analysis.WallVisibility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The actual angular flux bound on two visible graph pieces

The finite graph projection is passed through the selected polygons.
Every source is localized by an actual maximizing wall angle. The two
spatial pieces are disjoint, and the first-family projection error is
charged only to the two local angular intervals. Thus shrinking the
angular interval produces a second-order error under the proved bounded
curvature density; no ordinary perimeter continuity is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def nicheGraphProjection (U : Set Plane) (t l r : ℝ) : ℝ :=
  Real.cos t * (r - l) + Real.sin t *
    (sweptNiche U (Real.pi / 2) r - sweptNiche U (Real.pi / 2) l)

namespace AngularGrid

open FinitePolygon

theorem innerAngularMassOn_union_le (U : Set Plane) (grid : Finset QuarterAngle)
    (E F : Set ℝ) {l r : ℝ} (hlr : l ≤ r) :
    innerAngularMassOn U grid (E ∪ F) l r ≤
      innerAngularMassOn U grid E l r + innerAngularMassOn U grid F l r := by
  classical
  simp only [innerAngularMassOn, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h0 := innerSourceMassOn_nonneg U grid hlr j
  by_cases hE : fullAngle grid j ∈ E <;> by_cases hF : fullAngle grid j ∈ F <;>
    simp only [mem_union, hE, hF, or_self, or_true, true_or, or_false, false_or,
      if_true, if_false, zero_add, add_zero] <;> linarith

theorem localized_quarter_source_projection (grid : Finset QuarterAngle)
    {s t θ : ℝ} (hθ : θ ∈ Icc s t) (j : SourceIndex grid)
    (hj : sourceQuarterAngle (fullAngle grid j) ∈ Ioo s t) :
    fullAngle grid j ∈ Ioc (s + Real.pi / 2) (t + Real.pi / 2) ∨
      (fullAngle grid j ∈ Ioc s t ∧ Real.sin (fullAngle grid j - θ) ≤ t - s) := by
  rw [sourceQuarterAngle_fullAngle] at hj
  cases j with
  | inl u =>
    right
    refine ⟨⟨hj.1, hj.2.le⟩, ?_⟩
    exact (le_abs_self _).trans (Real.abs_sin_le_abs.trans
      (abs_le.mpr ⟨by change -(t - s) ≤ (u.val : ℝ) - θ; linarith [hj.1, hθ.2],
        by change (u.val : ℝ) - θ ≤ t - s; linarith [hj.2, hθ.1]⟩))
  | inr u =>
    left
    change s + Real.pi / 2 < (u.val : ℝ) + Real.pi / 2 ∧
      (u.val : ℝ) + Real.pi / 2 ≤ t + Real.pi / 2
    constructor <;> linarith [hj.1, hj.2]

theorem finiteGraphProjection_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} {level : ℕ → ℕ} {a b l r θ : ℝ}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hlevel : Tendsto level atTop atTop)
    (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
    Tendsto (fun n => finiteGraphProjection (U n) (dyadic (level n)) θ l r)
      atTop (𝓝 (nicheGraphProjection K θ l r)) := by
  have hleft := finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox
    (fun _ => hl) tendsto_const_nhds
  have hright := finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox
    (fun _ => hr) tendsto_const_nhds
  exact tendsto_const_nhds.add ((hright.sub hleft).const_mul (Real.sin θ))

/-- Every hypothesis about a visible piece concerns the actual limiting
wall family. The selected-source localization and the limiting angular
mass are proved from the actual selected sequence. -/
theorem nicheGraphProjection_add_le_curvature_of_selected_sequence
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
    nicheGraphProjection target θ l₁ r₁ + nicheGraphProjection target θ l₂ r₂ ≤
      (upperCurvature target).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * ((upperCurvature target).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (upperCurvature target).real (Ioc s t)) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hbox := fun n => (hU n).inBox
  have hwidth : 0 ≤ capWidth target := by
    unfold capWidth
    exact sub_nonneg.mpr (horizontalLeft_le_horizontalRight
      hTarget.isCap.nonempty hTarget.isCap.isCompact)
  have hFbox : Icc l₁ r₁ ∪ Icc l₂ r₂ ⊆ Icc a b := by
    intro x hx
    rcases hx with hx | hx <;>
      constructor <;> linarith [hx.1, hx.2]
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
      finiteGraphProjection (U n) (dyadic (level n)) θ l₁ r₁ +
        finiteGraphProjection (U n) (dyadic (level n)) θ l₂ r₂ ≤
      innerAngularMass (U n) (dyadic (level n)) (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * (innerAngularMass (U n) (dyadic (level n))
          (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
            innerAngularMass (U n) (dyadic (level n)) (Ioc s t)) := by
    filter_upwards [hpos, hlocal, hLl, hrR] with n hnpos hnlocal hnL hnR
    have hbound := finiteGraphProjection_add_le_sources (U n) (dyadic (level n))
      hnL.le h₁ hgap h₂ hnR.le hδ
      (fun x hx => hnpos x (Or.inl (Ioc_subset_Icc_self hx)))
      (fun x hx => hnpos x (Or.inr (Ioc_subset_Icc_self hx)))
      (fun x hx j hj => localized_quarter_source_projection _ hθ j
        (hnlocal x (Or.inl (Ioc_subset_Icc_self hx)) j hj))
      (fun x hx j hj => localized_quarter_source_projection _ hθ j
        (hnlocal x (Or.inr (Ioc_subset_Icc_self hx)) j hj))
    have hm := innerAngularMassOn_union_le (U n) (dyadic (level n))
      (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) (Ioc s t)
      (show horizontalLeft (U n) + capWidth (U n) / 4 ≤
        horizontalRight (U n) - capWidth (U n) / 4 by linarith)
    simp only [innerAngularMassOn_middle] at hbound hm
    exact hbound.trans (add_le_add_left (mul_le_mul_of_nonneg_left hm hδ) _)
  have hbase := innerAngularMass_Ioc_tendsto_of_canonical_maximum hTarget hheight haffine hTargetBox
    hU hHausdorff hlevel hc hrate hleft hright hst hregular
  have hcomp := innerAngularMass_Ioc_tendsto_of_canonical_maximum hTarget hheight haffine hTargetBox
    hU hHausdorff hlevel hc hrate hleft hright (by linarith : s + Real.pi / 2 ≤ t + Real.pi / 2) hshift
  have hg₁ := finiteGraphProjection_tendsto (θ := θ) hHausdorff hcap hTarget.isCap hlevel hbox
    (hFbox (Or.inl (left_mem_Icc.mpr h₁))) (hFbox (Or.inl (right_mem_Icc.mpr h₁)))
  have hg₂ := finiteGraphProjection_tendsto (θ := θ) hHausdorff hcap hTarget.isCap hlevel hbox
    (hFbox (Or.inr (left_mem_Icc.mpr h₂))) (hFbox (Or.inr (right_mem_Icc.mpr h₂)))
  exact le_of_tendsto_of_tendsto (hg₁.add hg₂)
    (hcomp.add ((hcomp.add hbase).const_mul (t - s))) hfinite

end AngularGrid

/-- The visible-piece inequality constructs its own selected polygons.
In particular it has no approximation or source-occupation premise. -/
theorem IsFullCapMaximizer.nicheGraphProjection_add_le_curvature
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
    nicheGraphProjection U θ l₁ r₁ + nicheGraphProjection U θ l₂ r₂ ≤
      (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * ((upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (upperCurvature U).real (Ioc s t)) := by
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      exact ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩ <;> dsimp [a, b] <;> linarith [hx.1, hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hab hbox
  exact AngularGrid.nicheGraphProjection_add_le_curvature_of_selected_sequence hU hheight haffine
    hbox hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate
    (by dsimp [a]; linarith) (by dsimp [b]; linarith) hθ hregular hshift
    hL h₁ hgap h₂ hR hpositive hmaximizers

end AmbidextrousSofa
