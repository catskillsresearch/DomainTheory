/-ai
A tagged token some of the pair of an index k and a token belongs to the tagged copy of a set at an index i only when k equals i.

Membership in the image supplies a token of the set whose tag equals the given token, so the first components of the two dependent pairs agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- A tagged token determines its summand index. -/
theorem index_of_some_mem_injI {i k : ι} {a : α k} {X : Set (α i)}
    (hmem : (some ⟨k, a⟩ : Option (Σ i, α i)) ∈ injI i X) : k = i := by
  obtain ⟨b, _, heq⟩ := hmem
  simp only [Option.some.injEq] at heq
  exact (congrArg Sigma.fst heq).symm

end Exercise629

end DomainTheory.NeighbourhoodSystems
