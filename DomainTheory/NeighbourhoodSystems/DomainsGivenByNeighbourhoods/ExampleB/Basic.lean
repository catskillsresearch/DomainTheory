/-ai
This file gathers and re-exports the binary neighbourhood system of Example 1.B: finite binary strings, cones and the prefix comparison of cones, the nested-or-disjoint family of cones, prepending a prefix to a set or a cone, the finite elements, and the operation of applying a prefix to an element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
import all Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.memB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.B
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.prepend
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.sigmaBot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.sigmaElt
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Str
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone_nil
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone_subset_cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone_trichotomy
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.B_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.B_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.memB_cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_prepend
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.prepend_cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.memB_prepend
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.prepend_nil

@[expose] public section

/-!
# Example 1.B (Scott 1981, PRG-19, §1) — binary sequences

Scott's recurring **binary** example, generalizing the finite binary tree of Example 1.4 to
*infinite* sequences. Take `Δ = Σ*` with `Σ = {0,1}` (the finite binary strings, `Λ` = the empty
string), and for `σ ∈ Σ*` let `σΣ*` be the set of all *extensions* of `σ`. The neighbourhoods are

`B = {σΣ* ∣ σ ∈ Σ*}`,

a neighbourhood being "all extensions of a fixed prefix `σ`". We encode `Σ* = List Bool`, the
empty sequence `Λ = []`, concatenation `στ = σ ++ τ`, and the *initial-segment* relation
`σ ⪯ τ` by mathlib's list-prefix order `σ <+: τ`. The cone `σΣ*` is `cone σ = {w ∣ σ <+: w}`.

Deliverables (all of the Example-1.B paragraph, lines 281–315 of the source):

* **Example 1.B / Exercise (`B` is a system).** `B : NeighborhoodSystem Str`, built from the
  prefix *trichotomy* via `ofNestedOrDisjoint` — any two cones are nested or disjoint.
* **`σ⊥` (the finite elements).** `sigmaBot σ = ↑(cone σ)`, the principal filter of `σΣ*`; its
  minimal neighbourhood is `σΔ = cone σ`.
* **Factoid `σ₀⊥ ⊆ σ₁⊥ ⟺ σ₀` initial segment of `σ₁`.** `sigmaBot_le_iff`.
* **Exercise (`σx ∈ |B|`).** `sigmaElt σ x`, and `sigmaElt σ ⊥ = σ⊥` (`sigmaElt_bot`) justifying
  the `σ⊥` notation.
* **Factoid `x = ⋃ₙ σₙ⊥`.** `mem_iff_exists_sigmaBot`: every `x ∈ |B|` is the union of the finite
  elements `σ⊥` with `σΣ* ∈ x` — the concrete "limit of finite approximations" in `|B|`. (The
  countable *chain* form, with `σₙ ⪯ σₙ₊₁` enumerated, needs choice and is left to the prose.)

Everything is **constructive** (`#print axioms ⊆ {propext, Quot.sound}`): list-prefix is decidable,
so the trichotomy is choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem













/-! ### Prepending a prefix: `σX = {στ ∣ τ ∈ X}`. -/






/-! ### The finite elements `σ⊥` and the initial-segment factoid. -/


/-! ### The operation `σx` (Scott's left-multiplication on elements). -/


/-! ### Every element is a union of its finite approximations `σ⊥`. -/
end DomainTheory.NeighbourhoodSystems.ExampleB
