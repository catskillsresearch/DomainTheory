
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.approxUnion
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_of_entSet

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem closure_le_of_subset {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (hsub : u ⊆ w) : sys.closure u hu ≤ sys.closure w hw :=
  sys.closure_le_of_entSet hu hw fun _ hy => sys.ent_refl hw (hsub hy)

end InfoSys
end DomainTheory.InformationSystems
