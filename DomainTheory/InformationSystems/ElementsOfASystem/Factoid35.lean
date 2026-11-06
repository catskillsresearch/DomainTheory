module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.subset_closure

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_35 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u : Finset α} (hu : u ∈ sys.Con),
      ↑u ⊆ (sys.closure u hu).carrier :=
  @subset_closure

end DomainTheory.InformationSystems.InfoSys
