module

public import AmbidextrousSofa.Analysis.FullTriangleArea
public import AmbidextrousSofa.Analysis.PartialTriangleScalar

@[expose] public section

/-!
# The proper joint floor payment in the actual three-angle comparison

The two endpoint lower bounds and their sum constrain the two endpoint
depths jointly. The entire floor loss of the two signed triangles is
retained and paid by that joint constraint. All support cuts, roof
integrals and niche triangles belong to the cap being compared.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.threeAngleScore_lt_of_full_triangles_and_endpoint_bounds
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 37 / 25 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hER : 1 / 3 + h / 2 ≤ capRoof U a)
    (hEL : 1 / 3 - 2 * h / 3 ≤ capRoof U (-a)) :
    intervalSpatialScore (capRoof U) (threeAngleBarrier U) (horizontalLeft U)
      (horizontalRight U) < referenceHalfAreaLower := by
  obtain ⟨hk0, hk1, hksq, hc0, hc1⟩ := fullTriangle_offset_bounds
  dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  obtain ⟨hq, hS⟩ := hU.threeAngleScore_le_full_triangles (by linarith only [ha0, hh1]) ha1 hh0
    hh1 hl hr hleft hright haffine hEP
  have hloss := partialTriangle_floor_loss_le (k := Real.sqrt 2 - 1) hh0 (by linarith only [hk1])
    (by linarith only [hc0, hk1] :
      1 / 3 ≤ 2 * fullTriangleCos (Real.sqrt 2 - 1) - (1 + (Real.sqrt 2 - 1)))
    (by linarith only [hc1, hk0]) (by linarith only [hER] : 1 - capRoof U a ≤ 2 / 3 - h / 2)
    (by linarith only [hEL] : 1 - capRoof U (-a) ≤ 2 / 3 + 2 * h / 3) (by linarith only [hEP])
  have hfin := fullTriangleRelaxation_add_partial_loss_lt ha0 hh0 hh1
    (by linarith only [hk0]) hksq (by linarith only [hc0]) (fullTriangleCos_quadratic hksq) hq
  linarith only [hS, hloss, hfin]

end AmbidextrousSofa
