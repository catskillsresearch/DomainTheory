/-ai
The output-union insertion step sends a pair of raw-token lists and an accumulator finset to the choice-free union of the finite set of the pair's second list with the accumulator.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

def lamOutUnionInsert [DecidableEq (RawLamToken α)] :
    List (RawLamToken α) × List (RawLamToken α) → Finset (RawLamToken α) →
      Finset (RawLamToken α)
  | p, acc => listToFinset p.2 ∪' acc

end InfoSys

end DomainTheory.InformationSystems
