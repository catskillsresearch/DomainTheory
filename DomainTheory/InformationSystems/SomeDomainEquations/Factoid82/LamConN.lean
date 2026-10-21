/-ai
Stage-n consistency is the stratification of Scott's clauses (4) through (7). At stage zero, the atom finset is consistent in A and there are no function tokens. At stage n+1, the finset is already consistent at stage n, or it has no atoms, every function token has stage-n consistent components, and every subcollection of function tokens with a stage-n consistent input union has a stage-n consistent output union.
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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Stage-`n` consistency (Scott (4)–(7), stratified). -/
def LamConN : ℕ → Finset (RawLamToken α) → Prop
  | 0, u => lamAtomFinset u ∈ A.Con ∧ lamFunFinset u = ∅
  | n + 1, u =>
      LamConN n u ∨
        (lamAtomFinset u = ∅ ∧
          (∀ p ∈ lamFunFinset u,
            LamConN n (listToFinset p.1) ∧ LamConN n (listToFinset p.2)) ∧
            ∀ s ⊆ lamFunFinset u,
              LamConN n (lamInputUnion s) → LamConN n (lamOutputUnion s))

end InfoSys

end DomainTheory.InformationSystems
