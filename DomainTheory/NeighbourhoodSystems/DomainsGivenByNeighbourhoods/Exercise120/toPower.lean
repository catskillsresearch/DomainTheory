module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.mem_upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The element of `|𝒟'|` corresponding to `x ∈ |𝒟|`: the filter `{↑W ∣ W ∈ x}`. -/
def toPower (x : V.Element) : V.powerSystem.Element where
  mem S := ∃ W, x.mem W ∧ S = V.upSet W
  sub := by rintro S ⟨W, hW, rfl⟩; exact ⟨W, x.sub hW, rfl⟩
  master_mem := ⟨V.master, x.master_mem, rfl⟩
  inter_mem := by
    rintro S T ⟨W1, hW1, rfl⟩ ⟨W2, hW2, rfl⟩
    exact ⟨W1 ∩ W2, x.inter_mem hW1 hW2, V.upSet_inter W1 W2⟩
  up_mem := by
    rintro S T ⟨W, hW, rfl⟩ hT hsub
    obtain ⟨W', hW', rfl⟩ := hT
    exact ⟨W', x.up_mem hW hW' ((V.upSet_subset_iff (x.sub hW)).mp hsub), rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
