module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

def genAtom {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) : ℕ → Set β
  | 0 => M
  | (n + 1) => genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n)

end DomainTheory.NeighbourhoodSystems
