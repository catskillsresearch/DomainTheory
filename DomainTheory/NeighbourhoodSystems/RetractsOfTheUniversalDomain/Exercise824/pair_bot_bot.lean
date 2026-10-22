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
