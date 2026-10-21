/-ai
The neighbourhood of a token belongs to an ideal element if and only if the underlying set of the token is contained in the set represented by the element.

If the neighbourhood belongs to the element, each member of the token lies in its closure and therefore in the represented set. Conversely, the token is finite, so some token has its neighbourhood in the element and contains the original token in its closure. That neighbourhood is then contained in the neighbourhood of the original token, and upward closure puts the latter neighbourhood in the element.
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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.subset_Cl
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Tok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.exists_tok_of_finite_subset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Key membership identity.** `C(G) ∈ x ↔ G ⊆ toC x`. Forward: `G ⊆ Ḡ ⊆ toC x`. Reverse: `G` is
finite, so the finite-subcover lemma gives `F` with `C(F) ∈ x` and `G ⊆ F̄`, whence `C(F) ⊆ C(G)`
and upward closure gives `C(G) ∈ x`. -/
theorem mem_nbhd_iff (x : (reprSystem C hInter hne).Element) (G : Tok C) :
    x.mem (nbhd C G.1) ↔ G.1 ⊆ toC C hInter hne x := by
  constructor
  · intro hx t ht
    rw [mem_toC]
    exact ⟨G, hx, subset_Cl C G.1 ht⟩
  · intro hsub
    obtain ⟨F, hF, hGF⟩ := exists_tok_of_finite_subset C hInter hne x G.2.1 hsub
    have hnsub : nbhd C F.1 ⊆ nbhd C G.1 := (nbhd_subset_iff C hInter F.2).mpr hGF
    exact x.up_mem hF ⟨G, rfl⟩ hnsub

end DomainTheory.NeighbourhoodSystems.Exercise222
