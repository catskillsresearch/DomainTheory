module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodCongrOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.BasicInst12

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15(iii) (Scott 1981, PRG-19).** Two domain isomorphisms induce one on the products:
`|𝒟₀ × 𝒟₁| ≃o |𝒟₀' × 𝒟₁'|`. -/
def prodCongrD (e₀ : V₀.Element ≃o V₀'.Element) (e₁ : V₁.Element ≃o V₁'.Element) :
    (prod V₀ V₁).Element ≃o (prod V₀' V₁').Element :=
  (prodEquiv V₀ V₁).trans ((prodCongrOrderIso e₀ e₁).trans (prodEquiv V₀' V₁').symm)

end DomainTheory.NeighbourhoodSystems
