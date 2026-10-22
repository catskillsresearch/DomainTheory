/-ai
The family of all master neighbourhoods is finitely supported.

The empty list is a support, since every coordinate is already the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem FinSupp.master : FinSupp D (fun i => (D i).master) := ⟨[], fun _ _ => rfl⟩

end Exercise629

end DomainTheory.NeighbourhoodSystems
