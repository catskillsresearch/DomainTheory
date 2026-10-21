/-ai
If a product token has least second component, inserting it adds its first component to the left projection.

A witness in the projection of the inserted set is the inserted token, which contributes its first component, or a token of the original set, which witnesses membership in the original projection. Conversely, the inserted token witnesses its own first component, and a witness for the original projection remains a witness after insertion.
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
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_fstFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem fstFinset_insert_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 = B.bot) :
    fstFinset A B (insert p u) = insert p.val.1 (fstFinset A B u) := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hx'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩))
  · intro hx
    rcases Finset.mem_insert.mp hx with hx' | hx'
    · exact (mem_fstFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hx'.symm⟩
    · rcases (mem_fstFinset A B).1 hx' with ⟨q, hq, hbot, hxq⟩
      exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hxq⟩

end InfoSys

end DomainTheory.InformationSystems
