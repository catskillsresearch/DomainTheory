module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`genAtom`'s own recursive equation, as a rewritable lemma** (mirrors `Theorem88.lean`'s
`atomU_succ`; `genAtom`'s `def` is a direct structural match on its `Nat` argument, so this holds by
`rfl`, but stating it separately lets `rw` fire on `Nat`-literal successor forms like `2 * n + 1 + 1`
without needing to unfold `genAtom` itself). -/
theorem genAtom_succ' {γ : Type*} (Z : ℕ → Set γ) (M : Set γ) (δ : ℕ → Bool) (n : ℕ) :
    genAtom Z M δ (n + 1) = genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n) := rfl

end DomainTheory.NeighbourhoodSystems
