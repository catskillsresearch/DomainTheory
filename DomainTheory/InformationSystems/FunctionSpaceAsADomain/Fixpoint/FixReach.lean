module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Reachability of `v` from `∅` by a finite `w`-chain. -/
def FixReach (w : Finset (FunToken A A)) (v : Finset α) : Prop :=
  ∃ n, FixChain A w n v

end InfoSys

end DomainTheory.InformationSystems
