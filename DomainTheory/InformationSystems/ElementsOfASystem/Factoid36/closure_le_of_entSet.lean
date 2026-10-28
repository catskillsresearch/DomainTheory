
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.approxUnion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem closure_le_of_entSet {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (h : sys.EntSet w u) : sys.closure u hu ≤ sys.closure w hw := by
  intro a ha
  exact sys.ent_trans hw hu h ha

end InfoSys
end DomainTheory.InformationSystems
