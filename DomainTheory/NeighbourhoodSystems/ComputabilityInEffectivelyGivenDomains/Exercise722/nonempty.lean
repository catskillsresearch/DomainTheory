/-ai
Every language in Scott's family is nonempty.

The proof is by induction on membership. The set of all words contains the empty word, a singleton contains its word, concatenation preserves nonempty languages, and an intersection is admitted only when it is already nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.concat_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- **Every member of `S` is non-empty.** (`Σ` and singletons are non-empty; concatenation preserves
non-emptiness; intersections are only admitted to `S` when non-empty.) This is what makes `S`
*positive*. -/
theorem InS.nonempty {X : Set (List Bool)} (h : InS X) : X.Nonempty := by
  induction h with
  | univ => exact ⟨[], trivial⟩
  | singleton σ => exact ⟨σ, rfl⟩
  | mul _ _ ihX ihY => exact concat_nonempty ihX ihY
  | inter _ _ hne _ _ => exact hne

end Exercise722

end DomainTheory.NeighbourhoodSystems
