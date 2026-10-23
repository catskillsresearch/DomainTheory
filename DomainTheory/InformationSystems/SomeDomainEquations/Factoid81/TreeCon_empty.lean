module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_empty : TreeCon A (∅ : Finset (TreeToken α)) :=
  TreeCon.left _ (by rw [atomFinset_empty]; exact A.con_empty)
    pairLFinset_empty pairRFinset_empty

end InfoSys

end DomainTheory.InformationSystems
