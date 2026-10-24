module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodCongrOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodUniqueOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.uniqueProdOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodCommD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodAssocD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodUnitD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitProdD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodCongrD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitSys_element_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.BasicInst12

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.15(iii).** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'`. -/
theorem Isomorphic.prod (h₀ : V₀ ≅ᴰ V₀') (h₁ : V₁ ≅ᴰ V₁') : prod V₀ V₁ ≅ᴰ prod V₀' V₁' :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨prodCongrD e₀ e₁⟩

end DomainTheory.NeighbourhoodSystems
