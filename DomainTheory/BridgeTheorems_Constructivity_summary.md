# Constructivity summary

| Bridge | Footprint | Notes |
| --- | --- | --- |
| Nbhd ↔ InfoSys (both directions) | + inherited `Classical.choice` | Decidable coding; Mathlib 4.33 `Finset` instance frontier |
| CL ↔ RoundFilter | `{propext, Quot.sound}` | Roundness is order-theoretic |
| InfoSys ↔ Ideal | + inherited `Classical.choice` | Factoids 4.4–4.5; type-level `Finset` frontier |
| Algebraic ⇒ CL | classical | 1972 topological `≪` |
| Product / function space (1982) | + inherited `Classical.choice` | No witness extraction in the maps |
| Separated sum (1982) | + `Classical.choice` | Token polarity trichotomy |
| Factoid 4.6 ApproxMap ↔ ScottContinuous | + inherited `Classical.choice` | Type-level `Finset` frontier |
| ScottMap conjugation | + `Classical.choice` | Via 1972 `ScottMap` |

Target discipline (from the 1982 package): prefer constructive proofs wherever Scott’s
1982 text emphasizes constructivity; call out classical frontiers explicitly rather than
hiding choice in automation.

Mathlib 4.33 makes `Finset.instSetLike` and `Finset.instPartialOrder` depend on
`Classical.choice`. Consequently `#print axioms` reports choice for declarations whose
types traverse `InfoSys`, even when their proof terms only manipulate explicit finite
data. Here “no witness extraction” distinguishes that inherited library-instance
footprint from genuine uses such as separated-sum polarity classification.
