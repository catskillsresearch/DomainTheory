/-ai
A finite set contained in the set represented by an ideal element is contained in the closure of some token whose neighbourhood belongs to that element.

Induct on the finite set. The empty set is contained in the closure of the empty token, whose neighbourhood belongs to every element. When an element is inserted, membership of that element in the represented set supplies a token, and the inductive hypothesis supplies a token for the remainder. The directedness step produces a token above both, and the insertion decomposition places the new element and the remainder inside its closure.
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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Tok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.botTok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.directed_step
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd_bot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Finite sets are captured by a single token.** A finite `s ⊆ toC x` is contained in some `F̄`
with `C(F) ∈ x` — the finite-subcover property of the directed union `toC x`. -/
theorem exists_tok_of_finite_subset (x : (reprSystem C hInter hne).Element) {s : Set τ}
    (hs : s.Finite) (hsub : s ⊆ toC C hInter hne x) :
    ∃ F : Tok C, x.mem (nbhd C F.1) ∧ s ⊆ Cl C F.1 := by
  revert hsub
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨botTok C hne, mem_nbhd_bot C hInter hne x, Set.empty_subset _⟩
  | @insert a s _ha _hsfin ih =>
    intro hsub
    have ha' : a ∈ toC C hInter hne x := hsub (Set.mem_insert a s)
    rw [mem_toC] at ha'
    obtain ⟨Fa, hFa, haCl⟩ := ha'
    obtain ⟨Fs, hFs, hsCl⟩ := ih (fun y hy => hsub (Set.mem_insert_of_mem a hy))
    obtain ⟨F₃, hF₃, hFaF₃, hFsF₃⟩ := directed_step C hInter hne x hFa hFs
    refine ⟨F₃, hF₃, ?_⟩
    rw [Set.insert_subset_iff]
    exact ⟨hFaF₃ haCl, hsCl.trans hFsF₃⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
