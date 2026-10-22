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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

@[simp] theorem toS_mem_inj₁ {z : (Dsharp D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (toS D hD z).mem (inj₁ (prodNbhd P Q)) ↔ z.mem (embPair P Q) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨P', Q', hP', hQ', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := hD X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · obtain ⟨hPP, hQQ⟩ := prodNbhd_injective (inj₁_injective heq)
      rw [hPP, hQQ]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hz⟩)

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
