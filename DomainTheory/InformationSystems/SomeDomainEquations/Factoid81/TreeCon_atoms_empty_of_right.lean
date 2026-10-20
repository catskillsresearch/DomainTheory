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

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_atoms_empty_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hP : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    atomFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR =>
    rcases hP with h | h
    · exact False.elim (h hL)
    · exact False.elim (h hR)
  | right _ hA _ _ => exact hA

end InfoSys

end DomainTheory.InformationSystems
