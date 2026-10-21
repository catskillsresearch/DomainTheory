/-ai
The i-th generator is the level set of height i + 1 whose mask selects the residues below 2 to the i + 1 that have bit i set.

A number has bit i set exactly when its residue modulo 2 to the i + 1 does, and that residue lies below 2 to the i + 1 and has bit i set exactly when it belongs to the mask.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.testBit_mod_two_pow_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- Every `generator i` is a `V`-neighbourhood: `generator i = levelSet (i+1) M` for the bitmask
`M` selecting exactly the residues `< 2^(i+1)` whose own bit `i` is set. -/
theorem generator_eq_levelSet (i : ℕ) :
    generator i = levelSet (i + 1) (bitmaskOf ((Finset.range (2 ^ (i + 1))).filter
      (fun ℓ => ℓ.testBit i))) := by
  ext n
  simp only [mem_generator, mem_levelSet, testBit_bitmaskOf, Finset.mem_filter, Finset.mem_range]
  rw [← testBit_mod_two_pow_succ]
  exact ⟨fun h => ⟨Nat.mod_lt n (Nat.two_pow_pos _), h⟩, fun h => h.2⟩

end DomainTheory.NeighbourhoodSystems
