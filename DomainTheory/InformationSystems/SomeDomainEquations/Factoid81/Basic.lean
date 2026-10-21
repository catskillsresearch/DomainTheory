/-ai
This file gathers and re-exports the basic development of Scott's Factoid 8.1, the information system of unlabelled binary trees with atoms from a given information system, arranged so that tokens, consistency, and entailment match the separated sum of that system with the product of the tree system with itself. It re-exports the product and the separated sum, the inductive tree tokens, tree consistency, the atom projection and the left and right pair projections, the tree bottom, the entailment payload and tree entailment, the tree information system, its unfolding, and its right-hand side, together with the membership, emptiness, monotonicity, insertion, and singleton lemmas for the three projections, the lemmas on empty, singleton, and subset consistency and on insertion of the bottom and of an entailed token, the comparisons between the atom projection and the pair projections, the membership and transitivity lemmas for entailment and its payload, the lemma that a payload with no atoms and no pairs is the bottom, the lemmas that a pair projection entailed from the other side is nonempty or contained in the bottom singleton, and the lemma that a nonempty set contained in the bottom singleton equals that singleton.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
import all DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeSystem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeUnfold
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeRhs
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_foldr_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_singleton_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_singleton_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_singleton_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_singleton_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_singleton_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_singleton_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_singleton_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_singleton_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_singleton_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairs_empty_of_left
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_atoms_empty_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_atom_con_of_atoms
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairL_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairR_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_insert_of_ent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload_of_no_atoms_no_pairs
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairL_ne_or_subset_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairR_ne_or_subset_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.eq_singleton_bot_of_subset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload_trans
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt_trans
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_subset

@[expose] public section

/-!
# Factoid 8.1 — tree / S-expression domain `T ≅ A + (T × T)`

**Scott 1982, §8.** Given `A`, the domain `T` of unlabelled binary trees with atoms
from `A` is defined so tokens, consistency, and entailment match the separated sum
of `A` with the product `T × T` (Scott clauses (1)–(12)). The domain equation then
holds by this matching: we package it as an `InfoSys` on an inductive token type
together with the unfolding map into `A + (T × T)`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


/-! ## Tokens (Scott §8 (1)–(3)) -/

variable {α : Type*} [DecidableEq α]


/-! ## Projections -/


/-! ## Consistency and entailment -/

variable (A : InfoSys α)


/-! ## Domain equation

Scott secures `T ≅ A + (T × T)` by choosing tokens so that `T` is literally the
sum-of-product system. Here `TreeToken` is the inductive presentation of that
tagging (clauses (1)–(3)), and `TreeCon`/`TreeEnt` are the sum×product clauses
((4)–(12)). Unfolding compares with the official `sumSystem` / `productSystem`
carriers; `pairL bot` and `pairR bot` both land on the unique product bottom,
matching Scott’s single `(Δ,(Δ,Δ))`.
-/


end InfoSys
end DomainTheory.InformationSystems
