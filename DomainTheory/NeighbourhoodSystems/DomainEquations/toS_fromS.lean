/-ai
Composing the forward map of Example 6.1 with the reverse map is the identity on the sum.

The two elements contain the same neighbourhoods. A neighbourhood of the composite is the master, which already belongs to the original element, or a left copy, recovered by the forward half of the zero-embedding characterization of the reverse map, or a right product copy, recovered by the forward half of the pair-embedding characterization. Conversely, the subfamily law splits a neighbourhood of the original element into the master, a left copy restored by the reverse half of the zero characterization, or a product neighbourhood restored by the reverse half of the pair characterization.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- `toS ∘ fromS = id`. -/
theorem toS_fromS (s : (sumSys D hD).Element) : toS D hD (fromS D hD s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromS_mem_embZero D hD hX).mp hs
    · exact (fromS_mem_embPair D hD hP hQ).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromS_mem_embZero D hD hX).mpr hW⟩)
    · obtain ⟨P, Q, hP, hQ, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (fromS_mem_embPair D hD hP hQ).mpr hW⟩)

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
