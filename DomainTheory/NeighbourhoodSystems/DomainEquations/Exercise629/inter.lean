/-ai
The pointwise intersection of two finitely supported families is finitely supported.

Concatenate the two support lists. Off that concatenation both families equal the master, so their intersection equals the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem FinSupp.inter {X X' : ∀ i, Set (α i)}
    (hX : FinSupp D X) (hX' : FinSupp D X') : FinSupp D (fun i => X i ∩ X' i) := by
  obtain ⟨l, hl⟩ := hX; obtain ⟨l', hl'⟩ := hX'
  -- Outside `l ++ l'` both factors are the master, so the intersection is too — fully constructive,
  -- no case split on the undecidable proposition `X i = master`.
  refine ⟨l ++ l', fun i hi => ?_⟩
  rw [List.mem_append, not_or] at hi
  simp only [hl i hi.1, hl' i hi.2, Set.inter_self]

end Exercise629

end DomainTheory.NeighbourhoodSystems
