module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def mkRight (y : β) : ProdToken A B :=
  ⟨(A.bot, y), ⟨Or.inl rfl⟩⟩

namespace mkRight

instance instLeftCommutativeInsert :
    LeftCommutative fun y : β =>
      (insert (mkRight A B y) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkRight A B x) (mkRight A B y) s⟩

end mkRight

end InfoSys

end DomainTheory.InformationSystems
