module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-- **Definition 7.2 (Scott 1981, PRG-19) — computable element.** Specializing to `f : 𝟙 → W`, the
condition becomes: the index set `{m ∣ Yₘ ∈ y}` of the element `y ∈ |W|` is recursively enumerable.
We take this as the definition of a *computable element*. -/
def IsComputableElement {W : NeighborhoodSystem β} (Q : ComputablePresentation W)
    (y : W.Element) : Prop :=
  REPred (fun m => y.mem (Q.X m))

end DomainTheory.NeighbourhoodSystems
