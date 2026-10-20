module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_empty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixReach_empty (w : Finset (FunToken A A)) : FixReach A w ∅ :=
  ⟨0, fixChain_empty A w⟩

end InfoSys

end DomainTheory.InformationSystems
