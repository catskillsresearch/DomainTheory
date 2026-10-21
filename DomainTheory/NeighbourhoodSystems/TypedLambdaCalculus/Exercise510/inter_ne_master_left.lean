/-ai
If a neighbourhood is other than the master, its intersection with any set is still other than the master.

If the intersection equalled the master, the neighbourhood would equal the master: it is contained in the master, and rewriting the master as the intersection shows that the intersection is contained in the neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A neighbourhood that is `⊆ Δ₀` and equals `Δ₀` exactly when it contains `Δ₀`. A proper factor
`X ≠ Δ₀` stays proper after intersecting with anything: `X ∩ X' ≠ Δ₀`. -/
theorem inter_ne_master_left {X X' : Set α} (hX : V₀.mem X) (hXne : X ≠ V₀.master) :
    X ∩ X' ≠ V₀.master := by
  intro h
  apply hXne
  refine Set.Subset.antisymm (V₀.sub_master hX) ?_
  rw [← h]; exact Set.inter_subset_left

end DomainTheory.NeighbourhoodSystems.Exercise510
