/-ai
A raw list of tokens, each assumed depth-well-formed, lifts to a finset of depth-well-formed lambda tokens. The empty list gives the empty finset, and a cons inserts the head, witnessed by the given hypothesis, into the lift of the tail.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamWF
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Lift a raw Con set to a finset of depth-WF tokens. -/
def listToLamDFinset :
    (xs : List (RawLamToken α)) →
      (∀ t ∈ xs, IsLamWF A t) → Finset (LamDToken A)
  | [], _ => ∅
  | t :: ts, h =>
      insert ⟨t, h t List.mem_cons_self⟩
        (listToLamDFinset ts fun w hw => h w (List.mem_cons_of_mem t hw))

end InfoSys

end DomainTheory.InformationSystems
