/-ai
The emptiness characteristic of two coded constraint lists selects, on whether the success component of the coded positive meet-fold equals one, between the bounded search through the negative list for an index whose inclusion test accepts the pair of the meet index with that index, and the constant one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.IPos_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFold_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFoldCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (cons : ℕ → ℕ)

variable (incl : ℕ → ℕ)

/-- **The full `DAtom`-emptiness decider.** `1` iff `DAtom (decodeList posC) (decodeList negC) =
∅`: either the positive meet is already inconsistent (`ok ≠ 1`), or the meet's index `idx` lies
inside some negative target (bounded existential over `decodeList negC`, via `existsListChar`). -/
def DAtomEmptyChar (posC negC : ℕ) : ℕ :=
  selectFn (isOne (meetFoldCode P cons posC).unpair.1)
    (existsListChar (fun t => incl (Nat.pair t.unpair.2 t.unpair.1))
      (meetFoldCode P cons posC).unpair.2 negC)
    1

end DomainTheory.NeighbourhoodSystems
