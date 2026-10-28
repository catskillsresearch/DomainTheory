module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
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

theorem pairR_ne_or_subset_bot {u v : Finset (TreeToken α)}
    (hEnts : ∀ y ∈ pairRFinset u, TreeEnt A v (.pairR y)) :
    pairRFinset v ≠ ∅ ∨ pairRFinset u ⊆ {.bot} := by
  revert hEnts
  induction pairRFinset u using Finset.induction with
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
