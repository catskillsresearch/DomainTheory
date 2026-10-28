module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems

abbrev DomainIso {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Type _ :=
  V₀.Element ≃o V₁.Element

namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def IsTotal (x : V.Element) : Prop := ∀ y, x ≤ y → y ≤ x
end

end NeighborhoodSystem

def Isomorphic {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Prop :=
  Nonempty (DomainIso V₀ V₁)

@[inherit_doc] infix:25 " ≅ᴰ " => Isomorphic

theorem Isomorphic.refl {α : Type*} (V : NeighborhoodSystem α) : V ≅ᴰ V :=
  ⟨OrderIso.refl _⟩

theorem Isomorphic.symm {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h : V₀ ≅ᴰ V₁) : V₁ ≅ᴰ V₀ :=
  h.elim fun e => ⟨e.symm⟩

theorem Isomorphic.trans {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} (h₀ : V₀ ≅ᴰ V₁) (h₁ : V₁ ≅ᴰ V₂) : V₀ ≅ᴰ V₂ :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨e₀.trans e₁⟩

end DomainTheory.NeighbourhoodSystems
end
