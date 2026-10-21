/-ai
The empty set is reachable by a fix chain for any finite set of function tokens.

It is the value of the chain of length zero.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixReach_empty (w : Finset (FunToken A A)) : FixReach A w ∅ :=
  ⟨0, fixChain_empty A w⟩

end InfoSys

end DomainTheory.InformationSystems
