/-ai
In Example 1.2 the neighbourhood {0} is distinct from the master neighbourhood.

If they were equal, the token 1 would belong to {0}, because it belongs to the master.

The neighbourhood {1} is distinct from the master neighbourhood.

If they were equal, the token 0 would belong to {1}, because it belongs to the master.

An element that contains {0} is the total element determined by {0}.

The two elements contain the same neighbourhoods. A neighbourhood of the given element is the master, {0}, or {1}. The last alternative meets {0} in the empty set, which is not a neighbourhood. Conversely the master belongs to every element, and {0} is the given membership.

An element that contains {1} is the total element determined by {1}.

The two elements contain the same neighbourhoods. A neighbourhood of the given element is the master, {0}, or {1}. The middle alternative meets {1} in the empty set, which is not a neighbourhood. Conversely the master belongs to every element, and {1} is the given membership.

The neighbourhoods {0} and {1} are distinct.

The token 0 belongs to {0}. Rewriting the assumed equality would put it in {1}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.elemZero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.elemOne
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.not_mem_empty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_not_subset_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_not_subset_one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one_not_subset_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero_not_subset_one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero_inter_one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one_inter_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.inter_eq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero_inter_one

@[expose] public section

/-!
# Example 1.2 (Scott 1981, PRG-19, §1)

Scott's first worked example: tokens `Δ = {0, 1}` and neighbourhoods
`𝒟 = {{0, 1}, {0}, {1}}`.

We construct the neighbourhood system, prove it satisfies Definition 1.1, and classify
its domain elements (Definition 1.6): there are exactly three filters, and exactly one
partial element — the bottom filter `{Δ}`.
-/

namespace DomainTheory.NeighbourhoodSystems.Example12










theorem zero_ne_master : zero ≠ master := by
  intro h
  have : (1 : Token) ∈ zero := h ▸ (by simp [master])
  simp [zero] at this

theorem one_ne_master : one ≠ master := by
  intro h
  have : (0 : Token) ∈ one := h ▸ (by simp [master])
  simp [one] at this












namespace neighborhoodSystem

open NeighborhoodSystem




theorem mem_zero_of_mem (x : neighborhoodSystem.Element) (h : x.mem zero) :
    x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · exact Or.inr hzero
    · have hxone : x.mem one := hone ▸ hx
      have := x.inter_mem h hxone
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

theorem mem_one_of_mem (x : neighborhoodSystem.Element) (h : x.mem one) :
    x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · have hxzero : x.mem zero := hzero ▸ hx
      have := x.inter_mem hxzero h
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
    · exact Or.inr hone
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

theorem zero_ne_one : zero ≠ (one : Set Token) := by
  intro h
  have h0 : (0 : Token) ∈ zero := by simp [zero]
  rw [h] at h0
  simp [one] at h0
end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
