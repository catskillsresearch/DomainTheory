/-ai
The positive index set of a list of indices is the set of indices whose neighbourhood is contained in the neighbourhood of every index in the list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The `idxSet`-atom of the *positive* constraints `pos`: indices `m` with `Xₘ ⊆ Xᵢ` for every
`i ∈ pos`. (The empty list gives `Set.univ`, matching `genAtom`'s depth-`0` value.) -/
def IPos (pos : List ℕ) : Set ℕ := {m | ∀ i ∈ pos, m ∈ idxSet P.X i}

end DomainTheory.NeighbourhoodSystems
