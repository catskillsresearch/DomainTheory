module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

@[simp] theorem some_mem_injI {i : ι} {a : α i} {X : Set (α i)} :
    (some ⟨i, a⟩ : Option (Σ i, α i)) ∈ injI i X ↔ a ∈ X := by
  constructor
  · rintro ⟨b, hb, heq⟩
    simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at heq
    rwa [heq] at hb
  · intro ha; exact ⟨a, ha, rfl⟩

end Exercise629

end DomainTheory.NeighbourhoodSystems
