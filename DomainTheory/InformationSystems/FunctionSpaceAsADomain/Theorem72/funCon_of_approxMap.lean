/-ai
A finite set of function tokens that all lie in the relation of an approximable map is consistent in the function space.

For a subset whose input union is consistent, the union lemma gives that the map relates that input union to the output union, and the codomain law places the output union in the consistency predicate.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.rel_input_output_union

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem funCon_of_approxMap (f : ApproximableMap A B) (w : Finset (FunToken A B))
    (hw : ∀ p ∈ w, f.rel p.val.1 p.val.2) : FunCon A B w :=
  fun s hs hin =>
    f.rel_cod (rel_input_output_union A B f s (fun q hq => hw q (hs hq)) hin)

end InfoSys

end DomainTheory.InformationSystems
