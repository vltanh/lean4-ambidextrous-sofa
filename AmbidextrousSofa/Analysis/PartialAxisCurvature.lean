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
    0 < partialAxisCutoff α w :=
  lt_min (axisCutoff_pos hw) (half_pos (TerminalAngle.pos α))

theorem IsSelectedPolygon.curvature_set_near_axes_le {target U : Set Plane}
    {boxLeft boxRight coefficient R w a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) {s : Set ℝ} (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) (hab : a ≤ b) (hsab : s ⊆ Icc a b) (hterminal : (α : ℝ) ∉ Icc a b)
    (haxis : ∀ t ∈ Icc a b, t ≤ axisCutoff w ∨ Real.pi - t ≤ axisCutoff w) :
    (upperCurvature U).real s ≤ (8 * R + 24) * (b - a + mesh α level) +
      ∑ j, selectionDefect target U α level coefficient j := by
  classical
  -- No middle facet is near an axis.
  have hmid : ∑ j ∈ Finset.univ.filter (fun j => fullAngle α (dyadic level) j ∈ Icc a b),
      middleOuterMass U α (dyadic level) j = 0 :=
    Finset.sum_eq_zero fun j hj => AngularGrid.middleOuterMass_eq_zero_near_axes hU.isCap
      (outerGrid α (dyadic level)) hU.polygon_eq hw hW j (haxis _ (Finset.mem_filter.mp hj).2)
  have h := hU.curvature_set_le_of_atoms hc hs htop hsab (innerSourceMass_nonneg hU.isCap α hαL _)
    fun j _ => hU.curvature_atom_le_mass hc j
  linarith [innerSourceMass_sum_interval_le hU.isCap α hαL hR hbox level hab hterminal]

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
  have := hεaxis.trans (min_le_left _ _)
  have := hεcut.trans (min_le_right _ _)
  simpa only [sub_zero] using hU.curvature_set_near_axes_le hc hR hbox hw hW
    (fun t ht => ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩) (fun h => by linarith [h.2, Real.pi_pos])
    hε Ioc_subset_Icc_self (fun h => by linarith [h.2, TerminalAngle.pos α])
    fun t ht => Or.inl (ht.2.trans hεaxis)

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
  have := hεaxis.trans (min_le_left _ _)
  simpa only [sub_sub_cancel] using hU.curvature_set_near_axes_le hc hR hbox hw hW
    (fun t ht => ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩) (fun h => by linarith [h.1, Real.pi_pos])
    (sub_le_self _ hε) Ico_subset_Icc_self (fun h => by linarith [h.1, Real.pi_pos])
    fun t ht => Or.inr (by linarith [ht.1])

end PartialGrid
end AmbidextrousSofa
