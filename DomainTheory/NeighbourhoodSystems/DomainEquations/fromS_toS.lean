module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- `fromS ∘ toS = id`. -/
theorem fromS_toS (z : (Dsharp D hD).Element) : fromS D hD (toS D hD z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact z.master_mem
    · exact (toS_mem_inj₀ D hD hX).mp hs
    · exact (toS_mem_inj₁ D hD hP hQ).mp hs
  · intro hW
    cases z.sub hW with
    | gamma => exact Or.inl rfl
    | @zero X hX => exact Or.inr (Or.inl ⟨X, hX, rfl, (toS_mem_inj₀ D hD hX).mpr hW⟩)
    | @pair P Q hP hQ => exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (toS_mem_inj₁ D hD hP hQ).mpr hW⟩)

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
