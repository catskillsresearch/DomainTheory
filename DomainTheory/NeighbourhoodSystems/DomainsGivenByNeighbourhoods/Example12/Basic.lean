module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
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

@[expose] public section

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
