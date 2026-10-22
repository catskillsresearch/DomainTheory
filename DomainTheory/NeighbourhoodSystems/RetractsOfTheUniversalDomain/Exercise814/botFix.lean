/-ai
The bottom fixed point of a closure operator is the image of the bottom element of the system. Idempotence of the retraction makes that image a fixed point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **The bottom of `Fix(a)`**: `a(⊥)`. -/
def botFix (h : ClosureOperator a) : FixSet a :=
  ⟨a.toElementMap ⊥, toElementMap_idem h.out.1 ⊥⟩

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
