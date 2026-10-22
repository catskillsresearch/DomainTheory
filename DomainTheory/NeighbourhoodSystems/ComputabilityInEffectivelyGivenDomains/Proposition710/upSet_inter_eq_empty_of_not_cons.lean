/-ai
If no enumerated neighbourhood is contained in the intersection of the neighbourhoods coded by a and by b, then the intersection of their down-sets is empty.

Rewrite the intersection of the down-sets by the down-set intersection law. A neighbourhood in both down-sets would be a neighbourhood contained in that intersection. Surjectivity of the enumeration supplies a code for it, and rewriting by that equality puts the corresponding enumerated neighbourhood inside the intersection, contradicting the hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- If `(a, b)` is *inconsistent* (no `𝒟`-neighbourhood below `X_a ∩ X_b`) then `↓X_a ∩ ↓X_b = ∅`. -/
theorem upSet_inter_eq_empty_of_not_cons {a b : ℕ}
    (h : ¬ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    V.upSet (P.X a) ∩ V.upSet (P.X b) = ∅ := by
  rw [V.upSet_inter]
  ext Z
  simp only [mem_upSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro hZmem hZsub
  obtain ⟨n, hn⟩ := P.surj hZmem
  exact h ⟨n, by rw [hn]; exact hZsub⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
