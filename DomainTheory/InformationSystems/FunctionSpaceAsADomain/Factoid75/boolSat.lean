module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def boolSat : BoolPoint → BoolToken → Prop
  | .undef, .bot => True
  | .undef, _ => False
  | .isTrue, .bot => True
  | .isTrue, .tru => True
  | .isTrue, .fls => False
  | .isFalse, .bot => True
  | .isFalse, .fls => True
  | .isFalse, .tru => False

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem boolSat.bot (p : BoolPoint) : boolSat p .bot := by
  cases p <;> trivial

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem boolSat.sing (t : BoolToken) : ∃ p, boolSat p t := by
  cases t with
  | bot => exact ⟨.undef, trivial⟩
  | tru => exact ⟨.isTrue, trivial⟩
  | fls => exact ⟨.isFalse, trivial⟩

end InfoSys

end DomainTheory.InformationSystems
