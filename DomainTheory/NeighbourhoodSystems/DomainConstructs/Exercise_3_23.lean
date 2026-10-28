module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_15
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

section
set_option linter.unusedVariables false

theorem example_323.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys) f
    (@DomainTheory.NeighbourhoodSystems.toUnit α V) :=
  @DomainTheory.NeighbourhoodSystems.toUnit_unique
end
end

end DomainTheory.NeighbourhoodSystems
end
