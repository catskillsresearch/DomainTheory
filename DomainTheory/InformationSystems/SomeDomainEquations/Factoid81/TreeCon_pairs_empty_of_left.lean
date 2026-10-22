module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_pairs_empty_of_left {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hA : atomFinset u ≠ ∅) :
    pairLFinset u = ∅ ∧ pairRFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR => exact ⟨hL, hR⟩
  | right _ hAt _ _ => exact False.elim (hA hAt)

end InfoSys

end DomainTheory.InformationSystems
