/-ai
A total tree over the n-letter alphabet Fin n is a function from finite words on that alphabet to a Boolean sign, so that every node, addressed by a finite selector, carries a genuine label.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

/-- A **total tree** over the alphabet `Σ = Fin n` (Scott's `n`-ary `±` tree): an assignment of a
`±` label (`Bool`, `true = +`) to every node, addressed by a finite selector `σ ∈ Σ*`. A tree is
*total* in Scott's sense (every node carries a genuine label), as opposed to the partial elements of
the domain `A` of `Example62A.lean` where labels may be `⊥`. -/
abbrev Tree (n : ℕ) : Type := List (Fin n) → Bool

end Example62Regular

end DomainTheory.NeighbourhoodSystems
