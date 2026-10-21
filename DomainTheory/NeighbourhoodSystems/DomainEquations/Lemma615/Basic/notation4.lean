/-ai
The infix notation ⊴ is introduced for the subdomain-embedding relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Trianglelefteq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq

end DomainTheory.NeighbourhoodSystems
