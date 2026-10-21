/-ai
The inverse conversion meets the pair embedding of two sharp neighbourhoods exactly when the sum element meets the right injection of their product neighbourhood.

If the converted element meets the pair embedding, the three forms of membership are Gamma, a zero copy, or a pair copy. A pair embedding is distinct from Gamma and from every zero embedding of a neighbourhood. In the pair-copy form, injectivity of the pair embedding identifies the two neighbourhoods, so the sum element meets the corresponding right injection. A right-injection membership is itself the pair-copy form of membership for the converted element.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_ne_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_ne_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embZero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

@[simp] theorem fromS_mem_embPair {s : (sumSys D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (fromS D hD s).mem (embPair P Q) ↔ s.mem (inj₁ (prodNbhd P Q)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P', Q', hP', hQ', heq, hs⟩)
    · exact absurd h0 (embPair_ne_Gamma D hD P Q)
    · exact absurd heq.symm (embZero_ne_embPair D hD hX' P Q)
    · obtain ⟨hPP, hQQ⟩ := embPair_injective heq
      rw [hPP, hQQ]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hs⟩)

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
