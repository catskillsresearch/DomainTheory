module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.Chain

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem IsDirected_of_IsChain {S : Set sys.Element} (h : sys.Chain S) : sys.IsDirected S := by
  intro x y hx hy
  rcases h.out x y hx hy with hxy | hyx
  · exact ⟨y, hy, hxy, le_rfl⟩
  · exact ⟨x, hx, le_rfl, hyx⟩

end InfoSys

end DomainTheory.InformationSystems
