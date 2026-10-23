module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
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

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_singleton (p : TreeToken α) : TreeCon A {p} := by
  induction p with
  | bot =>
    exact TreeCon.left _
      (by rw [atomFinset_singleton_bot]; exact A.con_empty)
      pairLFinset_singleton_bot pairRFinset_singleton_bot
  | atom x =>
    exact TreeCon.left _
      (by rw [atomFinset_singleton_atom]; exact A.con_sing x)
      (pairLFinset_singleton_atom x) (pairRFinset_singleton_atom x)
  | pairL t ih =>
    exact TreeCon.right _
      (atomFinset_singleton_pairL t)
      (by rw [pairLFinset_singleton_pairL]; exact ih)
      (by rw [pairRFinset_singleton_pairL]; exact TreeCon_empty A)
  | pairR t ih =>
    exact TreeCon.right _
      (atomFinset_singleton_pairR t)
      (by rw [pairLFinset_singleton_pairR]; exact TreeCon_empty A)
      (by rw [pairRFinset_singleton_pairR]; exact ih)

end InfoSys

end DomainTheory.InformationSystems
