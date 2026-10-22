/-ai
The generated atom of a family of sets, a master set, and a sign sequence is the master set at depth zero. At a successor depth it is the previous atom met with the next set of the family when the sign is true, and met with the complement of that set in the master set when the sign is false.
ai-/
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
