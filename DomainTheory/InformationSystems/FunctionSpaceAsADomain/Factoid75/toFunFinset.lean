module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Forget strict tokens to ordinary function-space tokens. -/
def toFunFinset (w : Finset (StrictFunToken A B)) : Finset (FunToken A B) :=
  ⟨Multiset.map (Subtype.val : StrictFunToken A B → FunToken A B) w.1,
    (Multiset.nodup_map_iff_of_injective Subtype.val_injective).2 w.nodup⟩

end InfoSys

end DomainTheory.InformationSystems
