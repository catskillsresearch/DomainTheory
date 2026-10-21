/-ai
If a finset of raw lambda tokens has at least one function token, then it is depth-consistent if and only if its atom finset is empty, every function token has depth-consistent input and output finsets, and every subcollection of function tokens with a depth-consistent input union has a depth-consistent output union.

Rewriting the definition of depth consistency selects the nonempty function-token branch.
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

theorem LamConDepth_of_fun_nonempty {u : Finset (RawLamToken α)}
    (hF : lamFunFinset u ≠ ∅) :
    LamConDepth A u ↔
      lamAtomFinset u = ∅ ∧
        (∀ p ∈ lamFunFinset u,
          LamConDepth A (listToFinset p.1) ∧ LamConDepth A (listToFinset p.2)) ∧
        (∀ s ⊆ lamFunFinset u,
          LamConDepth A (lamInputUnion s) → LamConDepth A (lamOutputUnion s)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  rw [LamConDepth.eq_1, dite_eq_right hF]

end InfoSys

end DomainTheory.InformationSystems
