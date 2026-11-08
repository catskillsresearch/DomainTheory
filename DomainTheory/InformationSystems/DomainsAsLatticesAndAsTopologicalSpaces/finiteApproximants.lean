module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.directedSup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.botElement_eq_closure_empty
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closures_directed
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_element

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def finiteApproximants (x : sys.Element) : Set sys.Element :=
  {y | ∃ (u : Finset α) (hu : u ∈ sys.Con), ↑u ⊆ x.carrier ∧ y = sys.closure u hu}

namespace finiteApproximants

theorem nonempty (x : sys.Element) : (sys.finiteApproximants x).Nonempty := by
  refine ⟨sys.botElement, ∅, sys.con_empty, ?_, botElement.eq_closure_empty sys⟩
  intro a ha
  exact False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha))

theorem directed (x : sys.Element) : sys.IsDirected (sys.finiteApproximants x) := by
  intro y₁ y₂ hy₁ hy₂
  obtain ⟨u, hu, huX, rfl⟩ := hy₁
  obtain ⟨v, hv, hvX, rfl⟩ := hy₂
  obtain ⟨w, hw, hwX, huw, hvw⟩ := sys.closures_directed x hu hv huX hvX
  exact ⟨sys.closure w hw, ⟨w, hw, hwX, rfl⟩, huw, hvw⟩

theorem eq_directedSup (x : sys.Element) :
    x = sys.directedSup (sys.finiteApproximants x)
      (nonempty sys x) (directed sys x) := by
  refine le_antisymm ?_ ?_
  · intro a ha
    have : a ∈ sys.approxUnion x := (sys.mem_element_iff_mem_closure x a).1 ha
    obtain ⟨u, hu, huX, ha'⟩ := this
    rw [directedSup.carrier_eq_union sys]
    exact ⟨sys.closure u hu, ⟨u, hu, huX, rfl⟩, ha'⟩
  · apply directedSup.le sys
    intro y hy
    obtain ⟨u, hu, huX, rfl⟩ := hy
    exact sys.closure_le_element x hu huX

end finiteApproximants

end InfoSys
end DomainTheory.InformationSystems
