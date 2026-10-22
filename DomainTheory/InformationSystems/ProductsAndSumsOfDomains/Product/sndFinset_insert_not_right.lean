module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_sndFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem sndFinset_insert_not_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 ≠ A.bot) :
    sndFinset A B (insert p u) = sndFinset A B u := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hy'⟩

end InfoSys

end DomainTheory.InformationSystems
