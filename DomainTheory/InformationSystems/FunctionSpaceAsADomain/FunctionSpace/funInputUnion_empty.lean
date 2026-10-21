/-ai
The input union of the empty set of function-space tokens is empty.

Both sides are definitionally the empty set.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


theorem funInputUnion_empty : funInputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
