module

public import AmbidextrousSofa.Analysis.InactiveNormals
public import AmbidextrousSofa.Analysis.JointCapMaximum

@[expose] public section

/-!
# Inactive-normal insertion for joint maxima

The literal cap variation by inactive-normal insertion keeps the whole
partial barrier, terminal first wall included, on the middle window. It
gives a supporting-normal necessary condition at every charged roof point
of a joint maximizer.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- A charged roof point below height one has a supporting normal whose middle wall is not
strictly inactive: otherwise the point could be raised while keeping the whole fixed-angle
partial barrier on the middle, which would strictly increase the score. -/
theorem IsJointCapMaximizer.exists_noninactive_normal_on_wing {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hlow : capRoof U x₀ < 1) :
    ∃ θ ∈ Icc 0 Real.pi,
      coordDot (x₀, capRoof U x₀) (unitNormal θ) = angleSupport U θ ∧
      0 ≤ middleWallSlack U (horizontalLeft U + capWidth U / 4)
        (horizontalRight U - capWidth U / 4) θ :=
  hU.isCap.exists_noninactive_normal_on_wing hU.angle_pos hU.angle_mem.2
    (fun _ hV => hU.score_le_same_angle hV) (by linarith [one_lt_M, hU.width_bounds.1]) hx₀ hlow

end AmbidextrousSofa
