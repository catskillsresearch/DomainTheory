/-ai
The second projection of an element of the pair space is monotone.

After rewriting membership in the second component, the assumed inequality supplies the second conjunct of the membership witness, and the first conjunct is unchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}









theorem snd_mono {z z' : (PairSpace (E := E)).Element} (h : z ≤ z') : z.snd ≤ z'.snd := by
  intro X hX
  rw [mem_snd] at hX ⊢
  exact ⟨hX.1, h _ hX.2⟩

end Exercise824
end DomainTheory.NeighbourhoodSystems
