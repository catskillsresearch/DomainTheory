/-ai
The denotation of the expression sigma is distinct from the denotation of containsZero. The one-letter word whose entry is true lies in the former and not in the latter.

If the denotations agreed, that word would belong to the denotation of sigma by mem_denote_sigma, and rewriting by the agreement would place it in the denotation of containsZero, which decide rejects.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.mem_denote_sigma

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


/-- **The emptiness decider cannot decide relation (i).** `Σ ≠ "contains 0"`, witnessed by `[1] ∈ Σ`
but `[1] ∉ Σ·{0}·Σ`. To *decide* this inequality one must detect a word in `Σ ∩ ("contains 0")ᶜ` —
i.e. in the complement language `{1}*` — but `{1}*` is **not** expressible in the fragment (no
complement, no star other than the full `Σ`). Hence no fragment-emptiness query exposes the
difference: deciding equivalence needs machinery (a product/complement DFA, or a derivative
bisimulation) that goes strictly beyond emptiness of fragment expressions. -/
theorem sigma_ne_containsZero : denote .sigma ≠ denote containsZero := by
  intro h
  have h1 : ([true] : List Bool) ∈ denote .sigma := mem_denote_sigma _
  rw [h] at h1
  exact absurd h1 (by decide)

end Exercise722
end DomainTheory.NeighbourhoodSystems
