module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-- **Definition 7.2 (Scott 1981, PRG-19) — computable map.** Relative to computable presentations
`P` of `V` and `Q` of `W`, an approximable map `f : V → W` is *computable* iff its neighbourhood
relation `Xₙ f Yₘ`, transported to the integer indices, is recursively enumerable. -/
def IsComputableMap {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) (f : ApproximableMap V W) : Prop :=
  REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

end DomainTheory.NeighbourhoodSystems
