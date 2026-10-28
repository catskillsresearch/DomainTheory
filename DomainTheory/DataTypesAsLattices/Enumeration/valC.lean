module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valRank
public import DomainTheory.DataTypesAsLattices.Enumeration.valStage_subset
public import DomainTheory.DataTypesAsLattices.Enumeration.valStage_eq_of_rank_le
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def valC : Pomega := fix valStep

namespace valC

theorem valNat (n : ℕ) : funOf valC (ofNat n) = valNat n := by
  rw [valC, fix, funOf.iUnion]
  apply subset_antisymm
  · intro k hk
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hk
    exact valStage_subset s n hs
  · intro k hk
    exact Set.mem_iUnion.mpr
      ⟨valRank n, (valStage_eq_of_rank_le n (valRank n) le_rfl).symm ▸ hk⟩

end valC

end DomainTheory.DataTypesAsLattices
