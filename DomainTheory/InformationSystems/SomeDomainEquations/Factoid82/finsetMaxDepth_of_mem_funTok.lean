module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst31
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.le_finsetMaxDepth_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_list_lt_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_list_lt_funTok_out

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem finsetMaxDepth_of_mem_funTok {u : Finset (RawLamToken α)}
    {xs ys : List (RawLamToken α)} (h : .funTok xs ys ∈ u) :
    finsetMaxDepth (listToFinset xs) < finsetMaxDepth u ∧
      finsetMaxDepth (listToFinset ys) < finsetMaxDepth u :=
  ⟨Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok xs ys) (le_finsetMaxDepth_of_mem h),
    Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok_out xs ys) (le_finsetMaxDepth_of_mem h)⟩

end InfoSys

end DomainTheory.InformationSystems
