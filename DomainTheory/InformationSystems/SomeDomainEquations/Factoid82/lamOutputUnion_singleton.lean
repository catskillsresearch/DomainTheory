/-ai
The output union of a singleton raw-token list pair is the finite set of tokens in that pair's second list.

Membership in the choice-free union of that finite set with the empty set is rewritten, by the membership rules for choice-free union and for the empty finset, as membership in the finite set itself.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamOutputUnion_singleton (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamOutputUnion ({p} : Finset (List (RawLamToken α) × List (RawLamToken α))) =
      listToFinset p.2 := by
  ext t
  change t ∈ listToFinset p.2 ∪' ∅ ↔ t ∈ listToFinset p.2
  simp only [mem_funion, Finset.notMem_empty, or_false]

end InfoSys

end DomainTheory.InformationSystems
