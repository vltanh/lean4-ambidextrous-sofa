module

public import AmbidextrousSofa.Analysis.PartialSourceCounting

@[expose] public section

/-!
# Punctured-axis curvature bounds for the actual proper polygons

The two visited source families have bounded total mass on an interval,
up to one vanishing mesh error. Near an axis no supporting face can meet
the middle window. The complete terminal wall remains outside the right
axis neighborhood by the explicit half-angle cutoff.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def partialAxisCutoff (α : TerminalAngle) (w : ℝ) : ℝ :=
  min (axisCutoff w) ((α : ℝ) / 2)

theorem partialAxisCutoff_pos (α : TerminalAngle) {w : ℝ} (hw : 0 < w) :
    0 < partialAxisCutoff α w := by
  apply lt_min (axisCutoff_pos hw)
  have hα := α.property.1
  linarith only [hα, Real.pi_pos]

theorem IsSelectedPolygon.curvature_set_near_axes_le {target U : Set Plane}
    {boxLeft boxRight coefficient R w a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U)
    {s : Set ℝ} (hs : s ⊆ Ioo 0 Real.pi) (htop : Real.pi / 2 ∉ s)
    (hab : a ≤ b) (hsab : s ⊆ Icc a b) (hterminal : (α : ℝ) ∉ Icc a b)
    (haxis : ∀ t ∈ s, t ≤ axisCutoff w ∨ Real.pi - t ≤ axisCutoff w) :
    (upperCurvature U).real s ≤ (8 * R + 24) * (b - a + mesh α level) +
      ∑ j, selectionDefect target U α level coefficient j := by
  classical
  let F := Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
    fullAngle α (dyadic level) j ∈ s)
  let G := Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
    fullAngle α (dyadic level) j ∈ Icc a b)
  have hFG : F ⊆ G := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsab (Finset.mem_filter.mp hj).2⟩
  have hinner : (∑ j ∈ F, innerSourceMass U α hαL (dyadic level) j) ≤
      (8 * R + 24) * (b - a + mesh α level) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hFG
      (fun j _ _ => innerSourceMass_nonneg hU.isCap α hαL (dyadic level) j)).trans
      (innerSourceMass_sum_interval_le hU.isCap α hαL hR hbox level hab hterminal)
  have herr : (∑ j ∈ F, selectionDefect target U α level coefficient j) ≤
      ∑ j, selectionDefect target U α level coefficient j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => selectionDefect_nonneg target U α level hc j)
  have hatom (j : SourceIndex α (dyadic level)) (hj : j ∈ F) :
      (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
        innerSourceMass U α hαL (dyadic level) j + selectionDefect target U α level coefficient j := by
    have hmid : middleOuterMass U α (dyadic level) j = 0 :=
      AngularGrid.middleOuterMass_eq_zero_near_axes hU.isCap (outerGrid α (dyadic level))
        hU.polygon_eq hw hW j (haxis _ (Finset.mem_filter.mp hj).2)
    simpa only [hmid, add_zero] using hU.curvature_atom_le_mass hc j
  calc
    (upperCurvature U).real s =
        ∑ j ∈ F, (upperCurvature U {fullAngle α (dyadic level) j}).toReal :=
      AngularGrid.upperCurvature_real_eq_sum_sources hU.isCap (outerGrid α (dyadic level))
        hU.polygon_eq hs htop
    _ ≤ ∑ j ∈ F, (innerSourceMass U α hαL (dyadic level) j +
        selectionDefect target U α level coefficient j) := Finset.sum_le_sum hatom
    _ = (∑ j ∈ F, innerSourceMass U α hαL (dyadic level) j) +
        ∑ j ∈ F, selectionDefect target U α level coefficient j := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hinner herr

theorem IsSelectedPolygon.curvature_right_axis_bound {target U : Set Plane}
    {a b coefficient R w ε : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hc : 0 ≤ coefficient) (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (hε : 0 ≤ ε)
    (hεcut : ε ≤ partialAxisCutoff α w) :
    (upperCurvature U).real (Ioc 0 ε) ≤
      (8 * R + 24) * (ε + mesh α level) + ∑ j, selectionDefect target U α level coefficient j := by
  have hεaxis : ε ≤ axisCutoff w := hεcut.trans (min_le_left _ _)
  have hεquarter : ε ≤ Real.pi / 4 := hεaxis.trans (min_le_left _ _)
  have hεα : ε < (α : ℝ) := by
    have h := hεcut.trans (min_le_right _ _)
    have hα := α.property.1
    linarith only [h, hα, Real.pi_pos]
  have hs : Ioc (0 : ℝ) ε ⊆ Ioo 0 Real.pi := by
    intro t ht
    exact ⟨ht.1, by linarith only [ht.2, hεquarter, Real.pi_pos]⟩
  have htop : Real.pi / 2 ∉ Ioc (0 : ℝ) ε := by
    intro h
    linarith only [h.2, hεquarter, Real.pi_pos]
  have hterminal : (α : ℝ) ∉ Icc (0 : ℝ) ε := fun h => (not_lt_of_ge h.2) hεα
  simpa only [sub_zero] using hU.curvature_set_near_axes_le hc hR hbox hw hW hs htop
    hε Ioc_subset_Icc_self hterminal (fun t ht => Or.inl (ht.2.trans hεaxis))

theorem IsSelectedPolygon.curvature_left_axis_bound {target U : Set Plane}
    {a b coefficient R w ε : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hc : 0 ≤ coefficient) (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (hε : 0 ≤ ε)
    (hεcut : ε ≤ partialAxisCutoff α w) :
    (upperCurvature U).real (Ico (Real.pi - ε) Real.pi) ≤
      (8 * R + 24) * (ε + mesh α level) + ∑ j, selectionDefect target U α level coefficient j := by
  have hεaxis : ε ≤ axisCutoff w := hεcut.trans (min_le_left _ _)
  have hεquarter : ε ≤ Real.pi / 4 := hεaxis.trans (min_le_left _ _)
  have hs : Ico (Real.pi - ε) Real.pi ⊆ Ioo 0 Real.pi := by
    intro t ht
    exact ⟨by linarith only [ht.1, hεquarter, Real.pi_pos], ht.2⟩
  have htop : Real.pi / 2 ∉ Ico (Real.pi - ε) Real.pi := by
    intro h
    linarith only [h.1, hεquarter, Real.pi_pos]
  have hterminal : (α : ℝ) ∉ Icc (Real.pi - ε) Real.pi := by
    intro h
    linarith only [h.1, hαL, hεquarter, Real.pi_pos]
  have h := hU.curvature_set_near_axes_le hc hR hbox hw hW hs htop
    (show Real.pi - ε ≤ Real.pi by linarith only [hε]) Ico_subset_Icc_self hterminal
    (fun t ht => Or.inr (by linarith only [ht.1, hεaxis]))
  simpa only [show Real.pi - (Real.pi - ε) = ε by ring] using h

end PartialGrid
end AmbidextrousSofa
