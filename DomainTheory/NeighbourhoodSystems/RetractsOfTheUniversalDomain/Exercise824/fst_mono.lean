/-ai
The first projection of the pair space is monotone.

Rewrite membership in the first projection. The first component of that data is unchanged, and the inequality of elements carries the second component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}


theorem fst_mono {z z' : (PairSpace (E := E)).Element} (h : z ≤ z') : z.fst ≤ z'.fst := by
  intro X hX
  rw [mem_fst] at hX ⊢
  exact ⟨hX.1, h _ hX.2⟩

end Exercise824
end DomainTheory.NeighbourhoodSystems
