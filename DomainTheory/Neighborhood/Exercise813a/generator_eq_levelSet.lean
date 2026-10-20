/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise812
public import DomainTheory.Neighborhood.Exercise812g4
public import DomainTheory.Neighborhood.Exercise813a.Basic
public import DomainTheory.Neighborhood.Exercise813a.testBit_mod_two_pow_succ

@[expose] public section


namespace DomainTheory.Neighborhood

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

end DomainTheory.Neighborhood
