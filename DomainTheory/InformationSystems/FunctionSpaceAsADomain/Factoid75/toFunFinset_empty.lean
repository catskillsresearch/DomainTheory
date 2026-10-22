/-ai
The underlying function-token set of the empty set of strict tokens is empty.

In both directions of extensionality, membership in an empty set is impossible. One direction invokes the membership characterization of the underlying set.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


theorem toFunFinset_empty :
    toFunFinset A B (∅ : Finset (StrictFunToken A B)) = (∅ : Finset (FunToken A B)) := by
  ext p
  constructor
  · intro hp
    rcases (mem_toFunFinset A B).1 hp with ⟨_, hq, _⟩
    exact False.elim (Finset.notMem_empty _ hq)
  · intro hp
    exact False.elim (Finset.notMem_empty _ hp)

end InfoSys
end DomainTheory.InformationSystems
