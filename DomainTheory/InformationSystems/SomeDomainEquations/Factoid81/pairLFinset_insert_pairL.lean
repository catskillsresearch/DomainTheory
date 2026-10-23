module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairLFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

theorem pairLFinset_insert_pairL (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairLFinset (insert (.pairL t) u) = insert t (pairLFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_pairLFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (TreeToken.pairL.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

end InfoSys

end DomainTheory.InformationSystems
