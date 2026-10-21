/-ai
This instance records that inserting the first component of a product token, as an operation on finite sets of the first system, is left commutative, by the commutativity of insertion in a finite set.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

instance instLeftCommutativeFstInsert :
    LeftCommutative fun p : ProdToken A B => (insert p.val.1 : Finset α → Finset α) :=
  ⟨fun p q s => insert_comm' p.val.1 q.val.1 s⟩

end InfoSys

end DomainTheory.InformationSystems
