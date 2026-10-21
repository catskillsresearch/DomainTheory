/-ai
The principal element of a neighbourhood is a compact element.

Compactness is the theorem that a principal element below a directed supremum already lies below some stage.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.principal_compact

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}


theorem principal_isCompactElt {X : Set γ} (hX : V.mem X) : IsCompactElt (V.principal hX) :=
  fun d hdir h => principal_compact hX d hdir h

end Algebraic
end DomainTheory.NeighbourhoodSystems
