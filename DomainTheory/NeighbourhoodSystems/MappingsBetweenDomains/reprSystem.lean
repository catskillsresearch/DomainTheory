/-ai
The representation neighbourhood system on the tokens of a family has as neighbourhoods exactly the neighbourhoods of tokens, and has as master the set of all tokens. The master contains the empty token and equals the neighbourhood of the empty set. If the neighbourhood of a token is contained in the intersection of the neighbourhoods of two tokens, that token lies in its own neighbourhood, so the union of the two underlying sets is contained in its closure, which belongs to the family, and the neighbourhood of that union is the intersection. Every neighbourhood is contained in the master.
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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Tok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.botTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

include hInter hne in
/-- **The representation neighbourhood system** `reprSystem` over `Δ = Tok C`: neighbourhoods are
exactly the `C(F)` for tokens `F`, the master is all of `Δ = C(∅)`. -/
def reprSystem : NeighborhoodSystem (Tok C) where
  mem N := ∃ F : Tok C, N = nbhd C F.1
  master := Set.univ
  master_nonempty := ⟨botTok C hne, Set.mem_univ _⟩
  master_mem := ⟨botTok C hne, (nbhd_empty C).symm⟩
  inter_mem := by
    rintro X Y Z ⟨F, rfl⟩ ⟨F', rfl⟩ ⟨F'', rfl⟩ hZsub
    have hF''mem : (F'' : Tok C) ∈ nbhd C F''.1 := subset_Cl C F''.1
    have h := hZsub hF''mem
    have hClF'' : Cl C F''.1 ∈ C := Cl_mem C hInter F''.2.2
    have hunionsub : F.1 ∪ F'.1 ⊆ Cl C F''.1 := Set.union_subset h.1 h.2
    refine ⟨⟨F.1 ∪ F'.1, F.2.1.union F'.2.1, Cl C F''.1, hClF'', hunionsub⟩, ?_⟩
    ext G
    simp only [mem_nbhd, Set.mem_inter_iff, Set.union_subset_iff]
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise222
