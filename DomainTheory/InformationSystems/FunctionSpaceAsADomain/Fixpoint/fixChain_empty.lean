/-ai
The empty set is a fix chain of length zero for any finite set of function tokens.

The length-zero clause of the definition is that equality, so the claim is definitional.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixChain_empty (w : Finset (FunToken A A)) : FixChain A w 0 ∅ :=
  rfl

end InfoSys

end DomainTheory.InformationSystems
