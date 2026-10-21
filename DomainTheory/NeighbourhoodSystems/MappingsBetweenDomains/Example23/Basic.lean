/-ai
This file gathers and re-exports the ingredients of the parity map from the binary neighbourhood system to the two-token domain: the codomain, the elements true, false, and bottom, the comparison of bottom with every element, the parity scanner and its clauses, stability of a committed scan under extension, the element selected by a scan value and its monotonicity under longer prefixes, and the approximable parity map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.trueElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.falseElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.valElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.parityMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.T
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.botElt_le
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.valElt_scan_mono

@[expose] public section

/-!
# Example 2.3 (Scott 1981, PRG-19, §2) — the parity map `f : B → T`

Scott's first approximable mapping. Reading a binary sequence left to right, count the number `n`
of `0`'s seen *before the first* `1`; the output is `true` if `n` is even, `false` if `n` is odd,
and `⊥` while the input is still an unbroken string of `0`'s (which has consistent extensions of
both parities). Concretely

`f(0ⁿ1⊥) = true` if `n` even, `false` if `n` odd; `f(0^∞) = ⊥`.

Here `B` is the binary system (`ExampleB`) and `T` is the two-token domain of Example 1.2, whose two
total elements we use as `true`/`false` and whose unique partial element is `⊥`.

We model the relation by a parity scanner `scan : Σ* → Option Bool`:
`scan` returns `none` while no `1` has appeared and `some b` (with `b` the parity-of-leading-zeros)
once the first `1` is found. The neighbourhood relation is

`X f Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ valElt (scan σ)`,

where `valElt none = ⊥`, `valElt (some true) = true`, `valElt (some false) = false`. The cone `σΣ*`
has a unique generating prefix (`cone_injective`), so this is well defined, and `scan` is *stable*
under extension (`scan_append`), which is exactly the monotonicity (Def 2.1(iii)).

Definition 2.1(i)–(iii) all check out, giving `parityMap : ApproximableMap B T`. (The `B`-side
reasoning is choice-free; `parityMap` nonetheless pulls `Classical.choice` through the concrete
codomain `T` of Example 1.2, whose `simp`/`fin_cases` proofs already do — pre-existing and harmless.)
-/

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


end DomainTheory.NeighbourhoodSystems.Example23
