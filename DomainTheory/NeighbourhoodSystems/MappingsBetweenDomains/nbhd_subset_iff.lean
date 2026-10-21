/-ai
For a token, its neighbourhood is contained in the neighbourhood of a set if and only if that set is contained in the closure of the token.

If the neighbourhoods are nested, the token lies in its own neighbourhood because it is contained in its closure, hence lies in the other neighbourhood. Conversely, if a token lies in the first neighbourhood and the set is contained in the closure of the original token, the closure of the new token belongs to the family and contains the original token, so it contains that closure and therefore contains the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.subset_Cl
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl_subset
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.IsTok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Tok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

include hInter in
/-- `C(F) ⊆ C(G) ↔ G ⊆ F̄`: comparison of neighbourhoods reduces to inclusion against closures. -/
theorem nbhd_subset_iff {F G : Set τ} (hF : IsTok C F) :
    nbhd C F ⊆ nbhd C G ↔ G ⊆ Cl C F := by
  constructor
  · intro h
    have hmem : (⟨F, hF⟩ : Tok C) ∈ nbhd C F := subset_Cl C F
    exact h hmem
  · intro hG H hH
    exact hG.trans (Cl_subset C (Cl_mem C hInter H.2.2) hH)

end DomainTheory.NeighbourhoodSystems.Exercise222
