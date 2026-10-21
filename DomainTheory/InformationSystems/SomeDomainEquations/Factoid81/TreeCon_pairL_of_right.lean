/-ai
If a consistent finite set of tree tokens has empty atom projection, its left pair projection is consistent.

Case on the consistency constructor. A left-consistent set has empty left pair projection, which is consistent. A right-consistent set gives the consistency of the left pair projection directly.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_empty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_pairL_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (_hA : atomFinset u = ∅) : TreeCon A (pairLFinset u) := by
  cases hu with
  | left _ _ hL _ => rw [hL]; exact TreeCon_empty A
  | right _ _ hL _ => exact hL

end InfoSys

end DomainTheory.InformationSystems
