module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
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
