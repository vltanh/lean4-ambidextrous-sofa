module

public import AmbidextrousSofa.Analysis.WallVisibility
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

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

theorem innerAngularMassOn_union_le (U : Set Plane) (grid : Finset QuarterAngle)
    (E F : Set ℝ) {l r : ℝ} (hlr : l ≤ r) :
    innerAngularMassOn U grid (E ∪ F) l r ≤
      innerAngularMassOn U grid E l r + innerAngularMassOn U grid F l r := by
  classical
  simp only [innerAngularMassOn, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h0 := innerSourceMassOn_nonneg U grid hlr j
  by_cases hE : fullAngle grid j ∈ E <;> by_cases hF : fullAngle grid j ∈ F <;> simp [hE, hF, h0]

theorem localized_quarter_source_projection (grid : Finset QuarterAngle)
    {s t θ : ℝ} (hθ : θ ∈ Icc s t) (j : SourceIndex grid)
    (hj : sourceQuarterAngle (fullAngle grid j) ∈ Ioo s t) :
    fullAngle grid j ∈ Ioc (s + Real.pi / 2) (t + Real.pi / 2) ∨
      (fullAngle grid j ∈ Ioc s t ∧ Real.sin (fullAngle grid j - θ) ≤ t - s) := by
  rw [sourceQuarterAngle_fullAngle] at hj
  rcases j with u | u
  · simp only [Sum.elim_inl, fullAngle, mem_Ioc] at hj ⊢
    exact Or.inr ⟨⟨hj.1, hj.2.le⟩, (le_abs_self _).trans (Real.abs_sin_le_abs.trans
      (abs_le.mpr ⟨by linarith [hj.1, hθ.2], by linarith [hj.2, hθ.1]⟩))⟩
  · simp only [Sum.elim_inr, fullAngle, mem_Ioc, add_lt_add_iff_right, add_le_add_iff_right] at hj ⊢
    exact Or.inl ⟨hj.1, hj.2.le⟩

theorem finiteGraphProjection_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} {level : ℕ → ℕ} {a b l r θ : ℝ}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hlevel : Tendsto level atTop atTop)
    (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
    Tendsto (fun n => finiteGraphProjection (U n) (dyadic (level n)) θ l r)
      atTop (𝓝 (nicheGraphProjection K θ l r)) :=
  tendsto_const_nhds.add (((finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox
    (fun _ => hr) tendsto_const_nhds).sub (finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel
      hbox (fun _ => hl) tendsto_const_nhds)).const_mul (Real.sin θ))

end AngularGrid

open AngularGrid in
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
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hwidth : 0 ≤ capWidth U := sub_nonneg.mpr hlr
  obtain ⟨a, b, hleft, hright, hbox⟩ : ∃ a b : ℝ, a < horizontalLeft U ∧
      horizontalRight U < b ∧ U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 :=
    ⟨_, _, sub_one_lt _, lt_add_one _, fun P hP => ⟨Icc_subset_Icc (sub_one_lt _).le
      (lt_add_one _).le (hU.isCap.fst_mem_Icc hP), hU.isCap.inStrip hP⟩⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    exists_selected_sequence hU (by linarith) hbox
  replace hlevel := tendsto_atTop_mono hlevel tendsto_id
  have hcap n : IsDownwardCap (V n) := (hV n).isCap
  have hFbox : Icc l₁ r₁ ∪ Icc l₂ r₂ ⊆ Icc a b := by
    rintro x (hx | hx) <;> constructor <;> linarith [hx.1, hx.2]
  have hF : IsCompact (Icc l₁ r₁ ∪ Icc l₂ r₂) := isCompact_Icc.union isCompact_Icc
  have hw := (hHausdorff.capWidth_tendsto hcap hU.isCap).div_const 4
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hδ : 0 ≤ t - s := sub_nonneg.mpr (hθ.1.trans hθ.2)
  have hbase := innerAngularMass_Ioc_tendsto_of_canonical_maximum hU hheight haffine hbox
    hV hHausdorff hlevel (fun n => (hc n).le) hrate hleft hright (hθ.1.trans hθ.2) hregular
  have hcomp := innerAngularMass_Ioc_tendsto_of_canonical_maximum hU hheight haffine hbox
    hV hHausdorff hlevel (fun n => (hc n).le) hrate hleft hright
    (by linarith [hθ.1, hθ.2] : s + Real.pi / 2 ≤ t + Real.pi / 2) hshift
  have hg {l r : ℝ} (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) := finiteGraphProjection_tendsto
    (θ := θ) hHausdorff hcap hU.isCap hlevel (fun n => (hV n).inBox) hl hr
  refine le_of_tendsto_of_tendsto
    ((hg (hFbox (.inl (left_mem_Icc.mpr h₁))) (hFbox (.inl (right_mem_Icc.mpr h₁)))).add
      (hg (hFbox (.inr (left_mem_Icc.mpr h₂))) (hFbox (.inr (right_mem_Icc.mpr h₂)))))
    (hcomp.add ((hcomp.add hbase).const_mul (t - s))) ?_
  filter_upwards [eventually_finiteBarrier_pos_on_compact hHausdorff hcap hU.isCap hlevel
      (fun n => (hV n).inBox) hF hFbox hpositive,
    eventually_innerSources_in_open_of_maximizers hHausdorff hcap hU.isCap hlevel
      (fun n => (hV n).inBox) hF hFbox isOpen_Ioo hmaximizers,
    (hl.add hw).eventually_lt_const hL, (hr.sub hw).eventually_const_lt hR]
    with n hnpos hnlocal hnL hnR
  have hbound := finiteGraphProjection_add_le_sources (V n) (dyadic (level n))
    hnL.le h₁ hgap h₂ hnR.le hδ
    (fun x hx => hnpos x (.inl (Ioc_subset_Icc_self hx)))
    (fun x hx => hnpos x (.inr (Ioc_subset_Icc_self hx)))
    (fun x hx j hj => localized_quarter_source_projection _ hθ j
      (hnlocal x (.inl (Ioc_subset_Icc_self hx)) j hj))
    (fun x hx j hj => localized_quarter_source_projection _ hθ j
      (hnlocal x (.inr (Ioc_subset_Icc_self hx)) j hj))
  have hm := innerAngularMassOn_union_le (V n) (dyadic (level n))
    (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) (Ioc s t)
    (hnL.le.trans (h₁.trans (hgap.trans (h₂.trans hnR.le))))
  simp only [innerAngularMassOn_middle] at hbound hm
  exact hbound.trans (add_le_add_right (mul_le_mul_of_nonneg_left hm hδ) _)

end AmbidextrousSofa
