/-ai
If a product token has least second component, the left projection of its singleton is the singleton of its first component.

The singleton is insertion into the empty set. The left-insertion lemma adds the first component to the projection of the empty set, and that projection is empty.
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
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset_insert_left

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem fstFinset_singleton_left (p : ProdToken A B) (hp : p.val.2 = B.bot) :
    fstFinset A B {p} = {p.val.1} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, fstFinset_insert_left A B ∅ p hp,
    fstFinset_empty]
  rfl

end InfoSys

end DomainTheory.InformationSystems
