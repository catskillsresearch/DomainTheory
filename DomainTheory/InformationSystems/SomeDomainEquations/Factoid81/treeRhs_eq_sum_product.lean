/-ai
The right-hand side of the tree domain equation equals the sum of A with the product of the tree system of A with itself.

The two sides are definitionally the same.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u




variable {α : Type*} [DecidableEq α]















































variable (A : InfoSys α)


























theorem treeRhs_eq_sum_product :
    treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
