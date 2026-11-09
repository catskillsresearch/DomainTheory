module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.InformationSystems.a_second_example
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst22

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

theorem not_ent_empty_fls : ¬ boolSystem.Ent ∅ BoolToken.fls := by
  intro ⟨_, hAll⟩
  exact hAll .undef (fun _ h => absurd h (Finset.notMem_empty _))

end InfoSys

end DomainTheory.InformationSystems
