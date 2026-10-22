/-ai
The family of the three-token system is not finitely consistent.

Finite consistency applied to the length-three sequence of the three neighbourhoods would supply a neighbourhood contained in their intersection. That intersection is empty, so the neighbourhood would be empty, while membership in the system is nonemptiness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.triple_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.triple_interUpTo_empty

@[expose] public section


set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


/-- **Exercise 1.18 — `family` is pairwise consistent but not consistent.** Its full triple has
empty intersection, so no `Z ∈ 𝒟` (i.e. no non-empty `Z`) lies below it. -/
theorem not_finitelyConsistent : ¬ triSys.FinitelyConsistent family := by
  intro h
  obtain ⟨Z, hZmem, hZsub⟩ := h 3 triple triple_mem
  have hZne : Z.Nonempty := hZmem
  rw [triple_interUpTo_empty, Set.subset_empty_iff] at hZsub
  rw [hZsub] at hZne
  exact Set.not_nonempty_empty hZne

end triSys
end DomainTheory.NeighbourhoodSystems
