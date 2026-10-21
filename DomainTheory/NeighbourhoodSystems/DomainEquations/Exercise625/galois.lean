/-ai
For a projection pair, the injection of an element x lies below an element y if and only if x lies below the projection of y.

In one direction, monotonicity of the projection applied to the inequality, rewritten by the identity that the projection of the injection of x equals x, gives the result. In the other direction, monotonicity of the injection applied to the inequality, composed with the injection of the projection of y lying below y, gives the result.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.proj_inj_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_proj_apply_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **Exercise 6.25, the Galois connection.** For `x ∈ |𝒟|`, `y ∈ |ℰ|`:
`g(x) ⊑ y ↔ x ⊑ h(y)`. So `g` (lower adjoint) and `h` (upper adjoint) determine each other.

`→`: apply the monotone `h` to `g(x) ⊑ y` and use `h(g(x)) = x`.
`←`: apply the monotone `g` to `x ⊑ h(y)` and use `g(h(y)) ⊑ y`. -/
theorem galois (P : ProjectionPair D E) (x : D.Element) (y : E.Element) :
    P.inj.toElementMap x ≤ y ↔ x ≤ P.proj.toElementMap y := by
  constructor
  · intro hxy
    have := P.proj.toElementMap_mono hxy
    rwa [P.proj_inj_apply x] at this
  · intro hxy
    exact (P.inj.toElementMap_mono hxy).trans (P.inj_proj_apply_le y)

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
