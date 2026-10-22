module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₁_nonempty {Y : Set β} (hY : Y.Nonempty) : (inj₁ Y : Set (Option (α ⊕ β))).Nonempty :=
  Set.Nonempty.image ir hY

end DomainTheory.NeighbourhoodSystems
