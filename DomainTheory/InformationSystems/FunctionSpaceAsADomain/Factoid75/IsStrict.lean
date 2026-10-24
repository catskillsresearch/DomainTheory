module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_botElement_emptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictify

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `f` is strict when `f(⊥) = ⊥`. -/
def IsStrict (A : InfoSys α) (B : InfoSys β) (f : ApproximableMap A B) : Prop :=
  f.toElement A.botElement = B.botElement

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

theorem IsStrict.condMap (x y : A.Element) : IsStrict boolSystem A (InfoSys.condMap A x y) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨_, _, hE, _, _⟩⟩
    have hEmp : EmptyEntails boolSystem u := fun t ht =>
      mem_botElement_emptyEntails boolSystem (hu (Finset.mem_coe.2 ht))
    exact emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _))
  · exact botElement.le A _

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

theorem IsStrict.strictify (f : ApproximableMap A B) :
    IsStrict A B (ApproximableMap.strictify A B f) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨_, _, hcase⟩⟩
    have huE : EmptyEntails A u := fun x hx =>
      mem_botElement_emptyEntails A (hu (Finset.mem_coe.2 hx))
    rcases hcase with hE | ⟨_, hn⟩
    · exact emptyEntails_mem_botElement B (hE Z (Finset.mem_singleton_self _))
    · exact False.elim (hn huE)
  · exact botElement.le B _

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
