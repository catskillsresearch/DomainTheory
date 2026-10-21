/-ai
Every neighbourhood of D-sharp is contained in the master.

Induction on the neighbourhood gives the three cases. The master is contained in itself. A zero-copy is contained in the master. A pair is contained in the master once both of its sides are.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset_Gamma

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- Every neighbourhood of `D^§` is a subset of the master `Γ` (Scott's `𝒟^§ ⊆ 𝒫(Γ)`). -/
theorem memS_subset_gamma {D : NeighborhoodSystem α} {W : Set (List Bool × α)}
    (hW : MemS D W) : W ⊆ Gamma D := by
  induction hW with
  | gamma => exact subset_rfl
  | zero hX => exact embZero_subset_Gamma hX
  | pair _ _ ihP ihQ => exact embPair_subset_Gamma ihP ihQ

end Example61

end DomainTheory.NeighbourhoodSystems
