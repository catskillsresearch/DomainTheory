module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Gamma_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- Under Scott's standing assumption `∅ ∉ 𝒟`, no neighbourhood of `D^§` is empty. -/
theorem memS_nonempty {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {W : Set (List Bool × α)} (hW : MemS D W) : W.Nonempty := by
  induction hW with
  | gamma => exact Gamma_nonempty hD
  | zero hX => exact embZero_nonempty (hD _ hX)
  | pair _ _ ihP _ => exact embPair_nonempty ihP

end Example61

end DomainTheory.NeighbourhoodSystems
