/-ai
Depth consistency of a finset of raw lambda tokens is defined by recursion on the maximum token depth, using decidable equality of finsets so that the empty branch does not invoke choice. If the finset contains no function tokens, it is consistent exactly when its atom finset is consistent in A. If it contains function tokens, its atom finset is empty, every function token has depth-consistent input and output finsets, and every subcollection of function tokens whose input union is depth-consistent has a depth-consistent output union. Each recursive call is on a finset of strictly smaller depth.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamFunFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst31
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_of_mem_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_inputUnion_lt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_outputUnion_lt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Depth-based consistency: FunCon in the recursive clause (Scott (7)).
Uses `decidableEq_finset` so the empty-fun branch does not pull `Classical.choice`. -/
def LamConDepth (u : Finset (RawLamToken α)) : Prop :=
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  if _hF : lamFunFinset u = ∅ then
    lamAtomFinset u ∈ A.Con
  else
    lamAtomFinset u = ∅ ∧
      (∀ p ∈ lamFunFinset u,
        LamConDepth (listToFinset p.1) ∧ LamConDepth (listToFinset p.2)) ∧
      (∀ s ⊆ lamFunFinset u,
        LamConDepth (lamInputUnion s) → LamConDepth (lamOutputUnion s))
termination_by finsetMaxDepth u
decreasing_by
  · exact (finsetMaxDepth_of_mem_funTok (mem_lamFunFinset.1 ‹_›)).1
  · exact (finsetMaxDepth_of_mem_funTok (mem_lamFunFinset.1 ‹_›)).2
  · exact finsetMaxDepth_inputUnion_lt ‹_› ‹_›
  · exact finsetMaxDepth_outputUnion_lt ‹_› ‹_›

end InfoSys

end DomainTheory.InformationSystems
