/-ai
A finite set of product tokens entails a product token when the set is product-consistent, the first system entails the first component from the left projection whenever the second component is least, and the second system entails the second component from the right projection whenever the first component is least.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdCon

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Entailment for the product system (Scott 6.1(iv'), (iv'')).
Includes `ProdCon` so both projections stay available for `ent_con`. -/
def ProdEnt (u : Finset (ProdToken A B)) (p : ProdToken A B) : Prop :=
  ProdCon A B u ∧
    (p.val.2 = B.bot → A.Ent (fstFinset A B u) p.val.1) ∧
      (p.val.1 = A.bot → B.Ent (sndFinset A B u) p.val.2)

end InfoSys

end DomainTheory.InformationSystems
