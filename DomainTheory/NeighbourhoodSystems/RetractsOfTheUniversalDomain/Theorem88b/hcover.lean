/-ai
A set belongs to D if and only if it equals the re-pointed enumeration at some index.

If the set belongs to D, surjectivity of the presentation names an index, and applying the index swap twice, which is the identity, shows that the set equals the re-pointed enumeration at the swapped index. Conversely, every value of the re-pointed enumeration is a neighbourhood of the re-pointed presentation, hence belongs to D.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)







theorem hcover : ∀ S, D.mem S ↔ ∃ n, S = e P n := by
  intro S
  constructor
  · intro hS
    obtain ⟨n, hn⟩ := P.surj hS
    exact ⟨eIdx P n, by show S = P.X (eIdx P (eIdx P n)); rw [eIdx_involutive P n]; exact hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact (P0 P).mem_X n

end DomainTheory.NeighbourhoodSystems
