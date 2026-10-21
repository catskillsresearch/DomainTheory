/-ai
The fade combinator is the approximable map from the product of the two-point system with a neighbourhood system into that system, obtained by packaging the two-variable fade relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade₂

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- **Example 8.4's `fade` combinator**, packaged as a genuine `ApproximableMap (prod O D) D`
via the Theorem 3.5 bridge (`ofMap₂`). -/
def fade : ApproximableMap (prod O D) D := ofMap₂ fade₂

end DomainTheory.NeighbourhoodSystems
