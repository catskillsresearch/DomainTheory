/-ai
Scott's monotonicity law states that if u is contained in v and x is contained in y, then the application of u at x is contained in the application of v at y.

Transitivity of inclusion combines monotonicity of application on the left with monotonicity of application on the right.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic
public import DomainTheory.DataTypesAsLattices.Graph.funOf_monotone_right
public import DomainTheory.DataTypesAsLattices.Graph.funOf_monotone_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (μ).** Application is monotone in both arguments. -/
theorem mu_law {u v x y : Pomega} (hu : u ⊆ v) (hx : x ⊆ y) :
    funOf u x ⊆ funOf v y :=
  subset_trans (funOf_monotone_left hu x) (funOf_monotone_right v hx)

end DomainTheory.DataTypesAsLattices
