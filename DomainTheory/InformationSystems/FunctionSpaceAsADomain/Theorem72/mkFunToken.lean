module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32

@[expose] public section

namespace DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

theorem mkFunToken.property (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    u ∈ A.Con ∧ v ∈ B.Con :=
  ⟨hu, hv⟩

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

def mkFunToken (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    FunToken A B :=
  ⟨(u, v), mkFunToken.property A B u v hu hv⟩

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

theorem mkFunToken.eq (p : FunToken A B) :
    mkFunToken A B p.val.1 p.val.2 p.property.1 p.property.2 = p :=
  Subtype.ext rfl

end InfoSys
end

end DomainTheory.InformationSystems
