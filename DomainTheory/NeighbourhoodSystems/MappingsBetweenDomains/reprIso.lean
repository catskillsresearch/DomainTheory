/-ai
The representation isomorphism identifies an ideal element of the representation system with the member of the family that it represents, and a member of the family with the ideal element produced by ofC. The two round trips are the identities of ofC after the representation map and of the representation map after ofC. The order is preserved and reflected because the represented set of one element is contained in the represented set of another if and only if the first element lies below the second: from the inclusion, a neighbourhood of the first element is the neighbourhood of a token whose underlying set sits in both represented sets, so the membership identity puts it in the second element, and from the order a token witnessing membership in the first represented set still belongs to the second element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd_iff
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC_ofC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofC_toC

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

include hDir in
/-- **Exercise 2.22 — the representation theorem.** `C`, ordered by inclusion, is order-isomorphic
to the domain `|reprSystem|`. The isomorphism sends `x ↦ ⋃ {F̄ ∣ C(F) ∈ x}` (`toC`) and
`X ↦ {C(F) ∣ F ⊆ X}` (`ofC`). -/
def reprIso : (reprSystem C hInter hne).Element ≃o {X : Set τ // X ∈ C} where
  toFun x := ⟨toC C hInter hne x, toC_mem C hInter hne hDir x⟩
  invFun X := ofC C hInter hne X.1 X.2
  left_inv x := ofC_toC C hInter hne hDir x
  right_inv X := Subtype.ext (toC_ofC C hInter hne X.1 X.2)
  map_rel_iff' := by
    intro a b
    show toC C hInter hne a ⊆ toC C hInter hne b ↔ a ≤ b
    constructor
    · intro hsub N hN
      have hmemD : (reprSystem C hInter hne).mem N := a.sub hN
      obtain ⟨G, rfl⟩ := hmemD
      have hGa : G.1 ⊆ toC C hInter hne a := (mem_nbhd_iff C hInter hne a G).mp hN
      exact (mem_nbhd_iff C hInter hne b G).mpr (hGa.trans hsub)
    · intro hab t ht
      rw [mem_toC] at ht ⊢
      obtain ⟨F, hF, htCl⟩ := ht
      exact ⟨F, hab _ hF, htCl⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
