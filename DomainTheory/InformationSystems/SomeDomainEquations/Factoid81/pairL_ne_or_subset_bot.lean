/-ai
If every token of the left pair projection of a finite set is sent by the left-pair constructor to a token entailed by a second finite set, then either the left pair projection of the second set is nonempty or the left pair projection of the first set is contained in the singleton of the bottom.

Induct on the left pair projection of the first set. The empty projection is contained in the singleton. If the projection is an element inserted into a smaller set, the entailment of the corresponding left-pair token has a payload disjunction: either the left pair projection of the second set is nonempty, or the inserted element is the bottom. In the latter case the inductive hypothesis on the smaller set, fed the remaining entailments, either gives a nonempty left pair projection of the second set or shows that the smaller set is contained in the singleton, and then every member of the inserted set is either the inserted element, hence the bottom, or a member of the smaller set.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem pairL_ne_or_subset_bot {u v : Finset (TreeToken α)}
    (hEnts : ∀ y ∈ pairLFinset u, TreeEnt A v (.pairL y)) :
    pairLFinset v ≠ ∅ ∨ pairLFinset u ⊆ {.bot} := by
  revert hEnts
  induction pairLFinset u using Finset.induction with
  | empty =>
    intro; exact Or.inr (Finset.empty_subset _)
  | insert y s hys ih =>
    intro hEnts
    have hy := hEnts y (Finset.mem_insert_self _ _)
    rcases hy.2.2.2.2 with ⟨hneV, _⟩ | ⟨rfl, _⟩
    · exact Or.inl hneV
    · rcases ih (fun z hz => hEnts z (Finset.mem_insert_of_mem hz)) with h | hsub
      · exact Or.inl h
      · refine Or.inr ?_
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact Finset.mem_singleton_self _
        · exact hsub hz

end InfoSys

end DomainTheory.InformationSystems
