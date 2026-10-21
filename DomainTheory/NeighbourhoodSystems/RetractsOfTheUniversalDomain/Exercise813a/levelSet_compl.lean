/-ai
The complement of a level set is the level set of the same height whose mask selects the residues below 2 to the height that the original mask does not select.

Failing the original bit test is the same as having residue below 2 to the height and failing the mask's bit test, which is membership in the complementary mask.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`levelSet` is closed under complement** (within the "`∅`-or-genuine" dichotomy every closure
fact in this development uses): the bitmask that selects exactly the residues `< 2^k` *not*
selected by `m`. -/
theorem levelSet_compl (k m : ℕ) :
    (levelSet k m)ᶜ = levelSet k (bitmaskOf ((Finset.range (2 ^ k)).filter
      (fun ℓ => ¬ m.testBit ℓ))) := by
  ext n
  simp only [Set.mem_compl_iff, mem_levelSet, testBit_bitmaskOf, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨fun h => ⟨Nat.mod_lt n (Nat.two_pow_pos _), h⟩, fun h => h.2⟩

end DomainTheory.NeighbourhoodSystems
