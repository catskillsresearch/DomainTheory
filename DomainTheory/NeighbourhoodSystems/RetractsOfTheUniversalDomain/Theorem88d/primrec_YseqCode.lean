/-ai
The code of Scott's Y sequence is primitive recursive.

Exponentiation by two is primitive recursive. The code fold, fed the pair of the depth with two to that power, is primitive recursive, and its second component agrees with the coded sequence after that pair is unpacked.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_yFold

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem primrec_YseqCode : Nat.Primrec (YseqCode P) := by
  have h2n : Nat.Primrec (fun n : ℕ => 2 ^ n) := primrec_two_pow Nat.Primrec.id
  refine (Nat.Primrec.right.comp ((primrec_yFold P).comp (Nat.Primrec.id.pair h2n))).of_eq
    fun n => ?_
  show ((yFold P (Nat.pair n (2 ^ n)).unpair.1 (Nat.pair n (2 ^ n)).unpair.2)).unpair.2 = YseqCode P n
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl

end DomainTheory.NeighbourhoodSystems
