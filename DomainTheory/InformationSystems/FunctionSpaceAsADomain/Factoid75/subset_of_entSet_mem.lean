/-ai
If a token set contained in an element entails a second token set, then the second set is contained in the element.

Each token of the second set is entailed by the first, and an element is deductively closed.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

theorem subset_of_entSet_mem {x : A.Element} {v v' : Finset α}
    (hv : ↑v ⊆ x.carrier) (hEnt : A.EntSet v v') : ↑v' ⊆ x.carrier := by
  intro y hy
  exact x.closed v y hv (hEnt y (Finset.mem_coe.1 hy))

end InfoSys

end DomainTheory.InformationSystems
