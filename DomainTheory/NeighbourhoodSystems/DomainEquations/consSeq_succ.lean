module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

@[simp] theorem consSeq_succ (a : V.Element) (b : (iterSys V).Element) (k : ℕ) :
    consSeq a b (k + 1) = component b k := rfl

end Exercise618

end DomainTheory.NeighbourhoodSystems
