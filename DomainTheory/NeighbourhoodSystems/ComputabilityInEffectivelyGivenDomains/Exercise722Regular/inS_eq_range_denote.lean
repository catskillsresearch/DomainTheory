/-ai
The members of S are exactly the nonempty denotations of expressions.

Extend by a language. If it lies in S, completeness supplies an expression denoting it, and membership in S supplies nonemptiness of that denotation. Conversely, a nonempty denotation lies in S by soundness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.InS_denote_of_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.InS_exists_denote

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


theorem inS_eq_range_denote : {X | InS X} = denote '' {e | (denote e).Nonempty} := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, by rw [he]; exact h.nonempty, he⟩
  · rintro ⟨e, hne, rfl⟩
    exact InS_denote_of_nonempty hne

end Exercise722
end DomainTheory.NeighbourhoodSystems
