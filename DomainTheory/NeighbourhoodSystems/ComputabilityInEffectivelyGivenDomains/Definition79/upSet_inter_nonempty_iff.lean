/-ai
The down-sets of X and Y have nonempty intersection if and only if some neighbourhood is contained in the intersection of X and Y.

Rewrite the intersection of the down-sets as the down-set of the intersection. In each direction the same neighbourhood is the witness of nonempty membership and of the existential statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Definition 7.9 (remark 1).** "`↓X ∩ ↓Y ≠ ∅` iff `{X, Y}` is consistent in `𝒟`." The
down-sets `↓X`, `↓Y` meet exactly when `X, Y` have a common lower neighbourhood `Z ⊆ X ∩ Y`. -/
theorem upSet_inter_nonempty_iff {X Y : Set α} :
    (V.upSet X ∩ V.upSet Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  rw [V.upSet_inter]
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
