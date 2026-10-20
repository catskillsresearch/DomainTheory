module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- `u ⊆ ū`. -/
theorem subset_closure {u : Finset α} (hu : u ∈ sys.Con) :
    ↑u ⊆ (sys.closure u hu).carrier :=
  fun _ hX => sys.ent_refl hu (Finset.mem_coe.1 hX)

end InfoSys
end DomainTheory.InformationSystems
