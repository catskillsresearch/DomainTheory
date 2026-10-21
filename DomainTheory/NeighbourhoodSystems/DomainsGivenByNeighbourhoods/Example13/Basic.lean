/-ai
In Example 1.3 the neighbourhood {1, 2} is distinct from the master neighbourhood.

If they were equal, the token 0 would belong to {1, 2}, because it belongs to the master.

The neighbourhood {2} is distinct from the master neighbourhood.

If they were equal, the token 0 would belong to {2}, because it belongs to the master.

The neighbourhood {2} is distinct from {1, 2}.

If they were equal, the token 1 would belong to {2}, because it belongs to {1, 2}.

The neighbourhood {2} is contained in {1, 2}.

Each of the three tokens is checked, and a token of {2} is a token of {1, 2}.

An element that contains {2} is the total element.

The two elements contain the same neighbourhoods. A neighbourhood of the given element is the master, {1, 2}, or {2}, all of which belong to the total element. Conversely the master belongs to every element, {1, 2} is recovered by upward closure from {2} along the inclusion of {2} in {1, 2}, and {2} is the given membership.

An element that contains {1, 2} but not {2} is the intermediate element.

The two elements contain the same neighbourhoods. A neighbourhood of the given element is the master or {1, 2}. It cannot be {2}, because the intersection of {1, 2} with {2} is {2}. Conversely the master belongs to every element, and {1, 2} is the given membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.elemTwelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.elemTwo
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master_not_subset_twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master_not_subset_two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve_not_subset_two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve_inter_two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two_inter_twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.inter_eq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve_inter_two

@[expose] public section

/-!
# Example 1.3 (Scott 1981, PRG-19, §1)

Scott's second worked example: tokens `Δ = {0, 1, 2}` and neighbourhoods
`𝒟 = {{0, 1, 2}, {1, 2}, {2}}`.

We construct the neighbourhood system, prove it satisfies Definition 1.1, and classify
its domain elements (Definition 1.6): there are exactly three filters in a linear chain
`⊥ < {Δ,{1,2}} < {Δ,{1,2},{2}}`, with token `2` the sole total element.

This is a concrete finite computation (`fin_cases`/`simp`); footprint
`[propext, Classical.choice, Quot.sound]` — same as Example 1.2.
-/

namespace DomainTheory.NeighbourhoodSystems.Example13









theorem twelve_ne_master : twelve ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ twelve := by
    rw [h]
    simp [master]
  simp [twelve] at hmem

theorem two_ne_master : two ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ two := by
    rw [h]
    simp [master]
  simp [two] at hmem

theorem two_ne_twelve : two ≠ twelve := by
  intro h
  have hmem : (1 : Token) ∈ two := by
    rw [h]
    simp [twelve]
  simp [two] at hmem











namespace neighborhoodSystem

open NeighborhoodSystem




theorem two_subset_twelve : two ⊆ twelve := by
  intro t ht
  fin_cases t <;> simp [two, twelve] at ht ⊢

theorem mem_two_of_mem (x : neighborhoodSystem.Element) (h : x.mem two) :
    x = elemTwo := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hX12 | htwo
    · exact Or.inl rfl
    · rw [hX12]; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr htwo)
  · intro hx
    rcases hx with rfl | hx | hx
    · exact x.master_mem
    · rw [hx]; exact x.up_mem h mem_twelve two_subset_twelve
    · rw [hx]; exact h

theorem mem_twelve_of_mem (x : neighborhoodSystem.Element) (htwelve : x.mem twelve)
    (htwo : ¬x.mem two) : x = elemTwelve := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hX12 | hX2
    · exact Or.inl rfl
    · exact Or.inr hX12
    · have hxo : x.mem two := hX2 ▸ hx
      have := x.inter_mem htwelve hxo
      rw [twelve_inter_two] at this
      exact absurd this htwo
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact htwelve
end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
