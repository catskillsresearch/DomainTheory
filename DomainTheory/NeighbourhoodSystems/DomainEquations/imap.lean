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

/-- `i : 𝒟 × 𝒟^∞ → 𝒟^∞`, the "cons" iso (`iterProdIso⁻¹`); the `T`-algebra structure map. -/
def imap (V : NeighborhoodSystem α) : ApproximableMap (prod V (iterSys V)) (iterSys V) :=
  ofIso (iterProdIso V).symm

end Exercise618

end DomainTheory.NeighbourhoodSystems
