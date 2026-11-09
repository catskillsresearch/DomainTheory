module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def mkLeft (x : α) : ProdToken A B :=
  ⟨(x, B.bot), ⟨Or.inr rfl⟩⟩

namespace mkLeft

instance instLeftCommutativeInsert :
    LeftCommutative fun x : α =>
      (insert (mkLeft A B x) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkLeft A B x) (mkLeft A B y) s⟩

end mkLeft

end InfoSys

end DomainTheory.InformationSystems
