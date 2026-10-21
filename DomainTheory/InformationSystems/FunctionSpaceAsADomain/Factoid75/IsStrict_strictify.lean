/-ai
The strictification of an approximable map is strict.

A token in the image of the bottom element comes from an input contained in the bottom element, hence empty-entailed. The strictification alternative is either empty entailment of the output token, which places it in the bottom element, or a denial of empty entailment of the input, which contradicts the previous step. The bottom element lies below every element.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_botElement_emptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictify

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

theorem IsStrict_strictify (f : ApproximableMap A B) :
    IsStrict A B (strictify A B f) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨_, _, hcase⟩⟩
    have huE : EmptyEntails A u := fun x hx =>
      mem_botElement_emptyEntails A (hu (Finset.mem_coe.2 hx))
    rcases hcase with hE | ⟨_, hn⟩
    · exact emptyEntails_mem_botElement B (hE Z (Finset.mem_singleton_self _))
    · exact False.elim (hn huE)
  · exact botElement_le B _

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
