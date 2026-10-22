module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **The least-set-bit search combinator.** `myFirstBit m N` is the smallest `ℓ < N` with
`m.testBit ℓ = true`, or `N` itself (a sentinel, since a genuine witness is always `< N`) if no
such `ℓ` exists. Folds over `i = 0, 1, …, N - 1` in increasing order (via `Nat.rec` on `N`,
mirroring `bExistsFn`'s recursion exactly): once a witness has been found (the running value is
`< i`), it is carried forward unchanged; otherwise (`ih = i`, nothing found yet) bit `i` itself is
tested, becoming the new witness if set, or `i + 1` (the new sentinel) if not. -/
def myFirstBit (m N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (myTestBit m i) i (i + 1)) ih) N

end DomainTheory.NeighbourhoodSystems
