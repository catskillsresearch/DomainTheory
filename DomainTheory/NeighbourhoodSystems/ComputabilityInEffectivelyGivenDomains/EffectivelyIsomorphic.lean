/-ai
Two computable presentations are effectively isomorphic when an effective isomorphism between them exists.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-- **Exercise 7.18 — effectively isomorphic.** `D` and `E` are effectively isomorphic when an
`EffectiveIso` exists. -/
def EffectivelyIsomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) : Prop :=
  Nonempty (EffectiveIso P Q)

end Exercise718

end DomainTheory.NeighbourhoodSystems
