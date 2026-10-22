/-ai
The singleton consisting of the false token is not empty-entailing in the Boolean system.

Empty entailment of that singleton would mean that the empty set entails false.
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


open ApproximableMap


theorem not_emptyEntails_singleton_fls :
    ¬ EmptyEntails boolSystem ({BoolToken.fls} : Finset BoolToken) :=
  fun h => not_ent_empty_fls (h .fls (Finset.mem_singleton_self _))

end InfoSys
end DomainTheory.InformationSystems
