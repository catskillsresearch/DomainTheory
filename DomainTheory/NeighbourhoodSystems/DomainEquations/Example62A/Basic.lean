/-ai
This file gathers and re-exports the development of Scott's equation A ≅ Aⁿ + Aⁿ: the flat n-fold product and its proper products, the inductive family MemA and the neighbourhood system Asys, the slot encoding embTuple, the maps toAA and fromAA, and the order isomorphism aaEquiv, together with the lemmas that support them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aaEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slot_list_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.nil_not_mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.tag_eq_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_tuple_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Apow
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apowNe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_fromAA

@[expose] public section

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — the generalisation `A ≅ Aⁿ + Aⁿ`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI.
After the staple equations `B ≅ B + B` and `C ≅ {{Λ}} + C + C` (see `Example62.lean`/`Example62C.lean`),
Scott proposes "a simple, yet interesting generalization of `B`": for any `n`, the domain equation

`A ≅ Aⁿ + Aⁿ`,

where `Aⁿ` is the `n`-fold cartesian power. He solves it concretely over `Σ* = {0,1}*` as the least
family

`A = {Σ*} ∪ ⋃_{i∈{0,1}} { i ⋃_{j<n} 1ʲ0 X_j ∣ X_j ∈ A for all j < n }`,

so a neighbourhood (other than the master `Σ*`) is a tag bit `i` (Scott's `+/−`, here `true`/`false`)
followed by `n` slots, slot `j` reached behind the self-delimiting prefix `1ʲ0`. An element of `A`
(other than `⊥`) is thus `±⟨a₀, …, a_{n-1}⟩`: an `n`-tuple of elements of `A`, in one of two copies.

This module delivers:

* **`npow V n`** — the flat `n`-fold product `Vⁿ` over `Fin n × β`, with neighbourhoods the proper
  products `prodN X = ⋃_j {j} × X_j`. (Closure under intersection is componentwise — no tags, so no
  non-emptiness needed.)
* **`Asys n hn`** — Scott's domain `A` over `{0,1}*` (the inductive family `MemA`), a neighbourhood
  system under `0 < n` (so there is a coordinate to witness non-emptiness, Scott's `∅ ∉ A`). The slot
  encoding is `embTuple`, parsed via the uniqueness lemma `slotPre_inj`.
* **`A_domain_equation`** — the order-isomorphism `aaEquiv : |A| ≃o |Aⁿ + Aⁿ|`, i.e.
  `Asys n hn ≅ᴰ sum (npow A n) (npow A n) …`, mirroring `Example61.dsharpEquiv`.

For `n = 1` this recovers `B ≅ B + B` (one slot per copy); the tree picture and the automata-theory
aside (eventually-periodic trees ↔ regular events) are formalised in `Example62Regular.lean`.

All *data* is choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

/-! ### The flat `n`-fold product `Vⁿ` over `Fin n × β`. -/

variable {β : Type*} {n : ℕ}


/-! ### Scott's slot encoding `i ⋃_{j<n} 1ʲ0 X_j` over `{0,1}*`. -/


variable {n : ℕ}


/-! ### The neighbourhood system `A` solving `A ≅ Aⁿ + Aⁿ`. -/


/-! ### The domain equation `A ≅ Aⁿ + Aⁿ`. -/


end Example62A
end DomainTheory.NeighbourhoodSystems
