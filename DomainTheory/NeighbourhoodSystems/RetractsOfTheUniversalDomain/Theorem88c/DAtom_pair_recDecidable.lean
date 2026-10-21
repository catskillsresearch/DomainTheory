/-ai
Emptiness of the D-atom of the re-pointed presentation on the lists with entries i, j and k is recursively decidable in the triple (i, j, k).

Pairing the positive-list code with the negative-list code is primitive recursive. Compose the D-atom decider of the re-pointed presentation with that pairing. Unpairing recovers the two codes, and decoding the encoded lists returns the lists [i, j] and [k].
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capPosCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capNegCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.primrec_capPosCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.primrec_capNegCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`DAtom (P0 P) [i, j] [k] = ∅` is recursively decidable in `(i, j, k)`.** Reindexes
`DAtom_recDecidable (P0 P)` (Part 5) along the codes of the fixed-shape lists `[i,j]`/`[k]`. -/
theorem DAtom_pair_recDecidable :
    RecDecidable₃ (fun i j k => DAtom (P0 P) [i, j] [k] = ∅) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (capPosCode t) (capNegCode t)) :=
    primrec_capPosCode.pair primrec_capNegCode
  have hp := (DAtom_recDecidable (P0 P)).comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd, capPosCode, capNegCode, decodeList_encodeList]

end DomainTheory.NeighbourhoodSystems
