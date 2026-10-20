module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The `n`-fold composition `fⁿ` of an endomap with itself:
`f⁰ = I_𝒟` and `f^{n+1} = f ∘ fⁿ`. -/
def iterMap (f : ApproximableMap V V) : ℕ → ApproximableMap V V
  | 0 => idMap V
  | (n + 1) => f.comp (f.iterMap n)

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
