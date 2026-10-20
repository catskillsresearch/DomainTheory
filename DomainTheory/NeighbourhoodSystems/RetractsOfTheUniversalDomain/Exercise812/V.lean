module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_affine
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.upsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Exercise 8.12's `V`**: the neighbourhood system over `ℕ` whose neighbourhoods are the
non-empty finite unions of residue classes `2^k ℕ + ℓ` (`ℓ < 2^k`). Bookkeeping-free via
`levelSet`: every finite union of `affine`-sets — even at *different* levels `kᵢ` — refines
(`levelSet_upsample`) to a single common level, so `V.mem X := ∃ k m, X = levelSet k m` already
captures every such union (`V_mem_iff_finiteUnion` below makes this precise). Closure under
intersection needs no consistency hypothesis (`levelSet_inter`), mirroring `Example78.lean`'s `PN`
rather than `Definition87.lean`'s `U`. -/
def V : NeighborhoodSystem ℕ where
  mem X := ∃ k m, X = levelSet k m ∧ X.Nonempty
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := ⟨0, 1, levelSet_zero_one.symm, Set.univ_nonempty⟩
  inter_mem := by
    rintro X Y Z ⟨k₁, m₁, rfl, -⟩ ⟨k₂, m₂, rfl, -⟩ ⟨k₃, m₃, rfl, hZne⟩ hZsub
    exact ⟨max k₁ k₂, upsample k₁ (max k₁ k₂) m₁ &&& upsample k₂ (max k₁ k₂) m₂,
      levelSet_inter k₁ m₁ k₂ m₂, hZne.mono hZsub⟩
  sub_master := by rintro X _; exact Set.subset_univ X

end DomainTheory.NeighbourhoodSystems
