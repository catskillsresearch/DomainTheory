/-ai
The fixed neighbourhood system of an approximable endomap a consists of those neighbourhoods of E that a relates to themselves. Its master neighbourhood is the master neighbourhood of E, which belongs because a relates the master neighbourhood to itself. The intersection of two members that is contained in a third neighbourhood of E belongs to E, and monotonicity sends each self-relation to that intersection, so the right-intersection law of a supplies the self-relation. Every member is contained in the master neighbourhood because it is a neighbourhood of E.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The candidate subdomain of Theorem 8.5's proof, `D = {X ∈ E ∣ X a X}`.** Built for *any*
approximable map `a : E → E` — the neighbourhood-system axioms need only `mono`/`inter_right` of
`a`, no projection or finitary hypothesis. (This is also exactly Theorem 8.6's `Fix(sub)` predicate
`X sub(f) X`, restated for a single map `a` in place of the function-space token `f`.) -/
def fixedNbhd (a : ApproximableMap E E) : NeighborhoodSystem α where
  mem X := E.mem X ∧ a.rel X X
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨E.master_mem, a.master_rel⟩
  inter_mem := by
    rintro X Y Z ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ ⟨hZE, _⟩ hZsub
    have hXYE : E.mem (X ∩ Y) := E.inter_mem hXE hYE hZE hZsub
    have h1 : a.rel (X ∩ Y) X :=
      a.mono hXa Set.inter_subset_left subset_rfl hXYE hXE
    have h2 : a.rel (X ∩ Y) Y :=
      a.mono hYa Set.inter_subset_right subset_rfl hXYE hYE
    exact ⟨hXYE, a.inter_right h1 h2⟩
  sub_master := fun h => E.sub_master h.1

end DomainTheory.NeighbourhoodSystems
