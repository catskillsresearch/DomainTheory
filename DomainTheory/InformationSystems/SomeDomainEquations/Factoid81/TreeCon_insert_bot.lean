/-ai
Inserting the tree bottom into a consistent finite set of tree tokens preserves consistency.

Case on the consistency constructor. In the left-consistent case, the insert-bottom lemmas leave the atom projection and both pair projections unchanged, so the same data witness left consistency of the inserted set. In the right-consistent case, the same rewrites leave the empty atom projection and the two consistent pair projections unchanged.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_bot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_insert_bot {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    TreeCon A (insert .bot u) := by
  cases hu with
  | left _ hA hL hR =>
    exact TreeCon.left _
      (by rw [atomFinset_insert_bot]; exact hA)
      (by rw [pairLFinset_insert_bot]; exact hL)
      (by rw [pairRFinset_insert_bot]; exact hR)
  | right _ hA hL hR =>
    exact TreeCon.right _
      (by rw [atomFinset_insert_bot]; exact hA)
      (by rw [pairLFinset_insert_bot]; exact hL)
      (by rw [pairRFinset_insert_bot]; exact hR)

end InfoSys

end DomainTheory.InformationSystems
