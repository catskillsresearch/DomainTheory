module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-- An element of an effectively given domain is computable when the indices of
neighbourhoods it contains are a recursively enumerable set. -/
class ComputableElement {W : NeighborhoodSystem β} (Q : ComputablePresentation W)
    (y : W.Element) : Prop where
  out : REPred (fun m => y.mem (Q.X m))

/-- An approximable map between effectively given domains is computable when the
neighbourhood relation is recursively enumerable in the two indices. -/
class ComputableMap {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) (f : ApproximableMap V W) : Prop where
  out : REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

end DomainTheory.NeighbourhoodSystems
