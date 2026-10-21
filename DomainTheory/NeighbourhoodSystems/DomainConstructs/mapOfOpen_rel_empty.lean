/-ai
The map of a set U of elements relates a neighbourhood X to the empty set if and only if X is a neighbourhood and the basic open of X is contained in U.

Unfolding the relation, the alternative that the output is the whole token set is impossible for the empty set, so the remaining alternative is the basic-open inclusion. Conversely, that inclusion is the empty-output alternative of the relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The decisive special case: `X (mapOfOpen U) ∅ ↔ [X] ⊆ U` (for a neighbourhood `X`). -/
theorem mapOfOpen_rel_empty (U : Set V.Element) (X : Set α) :
    (mapOfOpen V U).rel X ∅ ↔ V.mem X ∧ V.basicOpen X ⊆ U := by
  rw [mapOfOpen_rel]
  constructor
  · rintro ⟨hX, h⟩
    refine ⟨hX, ?_⟩
    rcases h with h | ⟨_, h⟩
    · exact absurd h Set.empty_ne_univ
    · exact h
  · rintro ⟨hX, h⟩
    exact ⟨hX, Or.inr ⟨rfl, h⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise325
