/-ai
A sharp neighbourhood related by the catamorphism is a neighbourhood of the sharp domain.

The argument inducts on the relation. The master clause is the master neighbourhood. The leaf clause is the zero embedding of a neighbourhood in the domain of the leaf map. The node clause is the paired embedding of the two neighbourhoods given by the inductive hypotheses.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Related inputs are `D^§`-neighbourhoods. -/
theorem gRel_dom {W Z} (h : GRel u v W Z) : MemS D W := by
  induction h with
  | gamma _ => exact MemS.gamma
  | leaf hrel => exact MemS.zero (u.rel_dom hrel)
  | node _ _ _ ihP ihQ => exact MemS.pair ihP ihQ

end Exercise717

end DomainTheory.NeighbourhoodSystems
