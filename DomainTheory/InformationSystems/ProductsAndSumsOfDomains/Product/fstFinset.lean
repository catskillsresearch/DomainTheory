/-ai
The left projection of a finite set of product tokens is the set of first components of those tokens whose second component is the least token of the second system, obtained by folding insertion over that filtered multiset, starting from the empty set.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Left projection of a finite set of product tokens (Scott 6.1). -/
def fstFinset (u : Finset (ProdToken A B)) : Finset α :=
  Multiset.foldr (fun p : ProdToken A B => insert p.val.1) (∅ : Finset α)
    (u.filter (fun p => p.val.2 = B.bot)).1

end InfoSys

end DomainTheory.InformationSystems
