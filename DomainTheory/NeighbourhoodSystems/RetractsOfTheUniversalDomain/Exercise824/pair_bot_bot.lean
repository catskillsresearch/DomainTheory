/-ai
The pairing of the two bottoms of the function space is the bottom of the pair space.

Element extensionality reduces the claim to membership. Rewrite membership in the pair and in the bottom. In one direction a witnessing product has both factors in the bottom, so both factors are the master and the product of the masters is the master. In the other direction the two masters of the function space lie in the bottom, and rewriting the neighbourhood as the master together with the product of the masters recovers it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}










theorem pair_bot_bot : pair ((funSpace E E).bot) ((funSpace E E).bot) = (PairSpace (E := E)).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨(funSpace E E).master, (funSpace E E).master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

end Exercise824
end DomainTheory.NeighbourhoodSystems
