/-ai
The graph of σ_j, applied to x, equals σ_j(x).

Theorem 1.2 (i), applied to Scott continuity of σ_j, identifies the graph with the map, and both sides are then evaluated at x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























theorem sigmaJ_app (j : ℕ) (x : Pomega) :
    funOf (graph (sigmaJ j)) x = sigmaJ j x := by
  simpa using congrArg (fun g => g x) (theorem_1_2_i (sigmaJ_isScottContinuous j))

end DomainTheory.DataTypesAsLattices
