/-ai
Passing to underlying function tokens preserves inclusion of finite sets of strict tokens.

A member of the smaller underlying set is the coercion of a member of the smaller set, and that member belongs to the larger set.
ai-/
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_toFunFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem toFunFinset_subset {s w : Finset (StrictFunToken A B)} (h : s ⊆ w) :
    toFunFinset A B s ⊆ toFunFinset A B w := by
  intro p hp
  rcases (mem_toFunFinset A B).1 hp with ⟨q, hq, rfl⟩
  exact (mem_toFunFinset A B).2 ⟨q, h hq, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
