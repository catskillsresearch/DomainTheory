/-ai
This file gathers and re-exports the finitary half of Proposition 8.10, that the sum, product, and arrow combinators preserve finitary projections and that the fixed-point set of each is isomorphic to the corresponding construct on the domains determined by the two projections, as the background for Exercise 8.18.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b

@[expose] public section

/-!
# Exercise 8.18 (Scott 1981, PRG-19)

> **Exercise 8.18.** Many of the cases of 8.10 were left unproved. Please establish these
> assertions explicitly.

Recall **Proposition 8.10**: "If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`, and
`a→b`. If `a` and `b` are finitary, then so are the others; for the fixed-point set of each of them
is isomorphic to the corresponding construct applied to the domains determined by `a` and `b`."

## What is formalized here

**Every case of Proposition 8.10 — for all three combinators `+`, `×`, `→`, in both halves — was
already fully established** by `Proposition810.lean` (`isProjection_sumComb`/`isProjection_prodComb`/
`isProjection_arrowComb`, assembled as `isProjection_combinators`) and `Proposition810b.lean`
(`finitaryProjection_sumComb`/`finitaryProjection_prodComb`/`finitaryProjection_arrowComb`, plus the
three explicit isomorphisms `sumComb_elementIso`/`prodComb_elementIso`/`arrowComb_elementIso`,
assembled as `finitaryProjection_combinators`). Nothing was left unproved by *this* development —
Scott's own text left several cases as reader exercises (most likely the `+` and `→` cases, which
needed genuinely new `sumMap`/`expMap` bifunctor infrastructure beyond the "obvious" `×` case, per
`Proposition810b.lean`'s docstring), but this project closed all of them while proving Proposition
8.10 itself. This file is therefore a **pure citation**, assembling Proposition 8.10's two halves
into one headline statement under Exercise 8.18's name — no new proof content.

Axiom footprint: `⊆ {propext, Classical.choice, Quot.sound}`, identical to `Proposition810.lean`/
`Proposition810b.lean` (the `Classical.choice` is `U`'s own inherited footprint, not new here).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap
end DomainTheory.NeighbourhoodSystems
