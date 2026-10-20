module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
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

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap



theorem strictify_toElement_le (f : ApproximableMap A B) (x : A.Element) :
    (strictify A B f).toElement x ≤ f.toElement x := by
  intro Z ⟨u, hu, ⟨_, _, hcase⟩⟩
  rcases hcase with hE | ⟨hf, _⟩
  · exact (botElement_le B (f.toElement x))
      (emptyEntails_mem_botElement B (hE Z (Finset.mem_singleton_self _)))
  · exact ⟨u, hu, hf⟩

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
