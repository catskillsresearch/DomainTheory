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

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamInputUnion_singleton (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamInputUnion ({p} : Finset (List (RawLamToken α) × List (RawLamToken α))) =
      listToFinset p.1 := by
  ext t
  change t ∈ listToFinset p.1 ∪' ∅ ↔ t ∈ listToFinset p.1
  simp only [mem_funion, Finset.notMem_empty, or_false]

end InfoSys

end DomainTheory.InformationSystems
