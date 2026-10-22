module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset_insert_right

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem sndFinset_singleton_right (p : ProdToken A B) (hp : p.val.1 = A.bot) :
    sndFinset A B {p} = {p.val.2} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, sndFinset_insert_right A B ∅ p hp,
    sndFinset_empty]
  rfl

end InfoSys

end DomainTheory.InformationSystems
