/-ai
Every element is the directed supremum of its finite approximants.

Every token of the element lies in some finite approximation, and the carrier of the directed supremum is the union of the carriers, so the element lies below the supremum. Each finite approximant lies below the element, so the supremum lies below the element.
ai-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.nonempty_finiteApproximants
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.directed_finiteApproximants

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.directedSup_le
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_element
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- **Factoid 4.5 / algebraicity.** `x` is the directed lub of its finite approximants. -/
theorem eq_directedSup_finiteApproximants (x : sys.Element) :
    x = sys.directedSup (sys.finiteApproximants x)
      (sys.nonempty_finiteApproximants x) (sys.directed_finiteApproximants x) := by
  refine le_antisymm ?_ ?_
  · -- x ≤ directedSup: every token of x lies in some ū ⊆ x
    intro a ha
    have : a ∈ sys.approxUnion x := (sys.mem_element_iff_mem_closure x a).1 ha
    obtain ⟨u, hu, huX, ha'⟩ := this
    rw [sys.directedSup_carrier_eq_union]
    exact ⟨sys.closure u hu, ⟨u, hu, huX, rfl⟩, ha'⟩
  · -- directedSup ≤ x: each approximant is ≤ x
    apply sys.directedSup_le
    intro y hy
    obtain ⟨u, hu, huX, rfl⟩ := hy
    exact sys.closure_le_element x hu huX

end InfoSys
end DomainTheory.InformationSystems
