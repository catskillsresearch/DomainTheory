module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_fstFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem fstFinset_insert_not_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 ≠ B.bot) :
    fstFinset A B (insert p u) = fstFinset A B u := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hx'⟩

end InfoSys

end DomainTheory.InformationSystems
