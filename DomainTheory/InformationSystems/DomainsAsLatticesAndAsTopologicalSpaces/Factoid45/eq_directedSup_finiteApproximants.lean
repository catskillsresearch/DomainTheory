
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.finiteApproximants
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.nonempty_finiteApproximants
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.directed_finiteApproximants

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.directedSup
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_element
@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem eq_directedSup_finiteApproximants (x : sys.Element) :
    x = sys.directedSup (sys.finiteApproximants x)
      (sys.nonempty_finiteApproximants x) (sys.directed_finiteApproximants x) := by
  refine le_antisymm ?_ ?_
  ·
    intro a ha
    have : a ∈ sys.approxUnion x := (sys.mem_element_iff_mem_closure x a).1 ha
    obtain ⟨u, hu, huX, ha'⟩ := this
    rw [directedSup.carrier_eq_union sys]
    exact ⟨sys.closure u hu, ⟨u, hu, huX, rfl⟩, ha'⟩
  ·
    apply directedSup.le sys
    intro y hy
    obtain ⟨u, hu, huX, rfl⟩ := hy
    exact sys.closure_le_element x hu huX

end InfoSys
end DomainTheory.InformationSystems
