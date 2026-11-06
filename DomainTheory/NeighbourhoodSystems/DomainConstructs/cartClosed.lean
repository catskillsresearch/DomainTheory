module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
section
variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

instance : Subsingleton (ApproximableMap V unitSys) :=
  ⟨fun _ _ => ext_of_toElementMap fun _ => Subsingleton.elim _ _⟩

instance : Unique (ApproximableMap V unitSys) where
  default := constMap V (default : unitSys.Element)
  uniq _ := Subsingleton.elim _ _

def homAdjunction (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) :=
  curryEquiv V₀ V₁ V₂

def toUnit : ApproximableMap V unitSys := default

theorem toUnit_unique (f : ApproximableMap V unitSys) : f = toUnit V := Subsingleton.elim _ _
end

end

end DomainTheory.NeighbourhoodSystems
end
