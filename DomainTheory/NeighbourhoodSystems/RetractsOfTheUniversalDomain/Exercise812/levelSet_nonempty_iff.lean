module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem







theorem levelSet_nonempty_iff {k m : ℕ} :
    (levelSet k m).Nonempty ↔ ∃ ℓ < 2 ^ k, m.testBit ℓ = true := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n % 2 ^ k, Nat.mod_lt n (by positivity), hn⟩
  · rintro ⟨ℓ, hℓ, hm⟩
    exact ⟨ℓ, by rw [mem_levelSet, Nat.mod_eq_of_lt hℓ]; exact hm⟩

end DomainTheory.NeighbourhoodSystems
