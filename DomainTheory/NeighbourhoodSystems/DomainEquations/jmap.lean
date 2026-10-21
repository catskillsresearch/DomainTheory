/-ai
The splitting map from the infinite iterate to the product of the system with the iterate is the approximable map induced by the product isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `j : 𝒟^∞ → 𝒟 × 𝒟^∞`, the splitting iso (`iterProdIso`). -/
def jmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (prod V (iterSys V)) :=
  ofIso (iterProdIso V)

end Exercise618

end DomainTheory.NeighbourhoodSystems
