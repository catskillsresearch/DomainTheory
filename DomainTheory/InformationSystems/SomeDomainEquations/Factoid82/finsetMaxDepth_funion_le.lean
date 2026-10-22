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

theorem finsetMaxDepth_funion_le (u v : Finset (RawLamToken α)) :
    finsetMaxDepth (u ∪' v) ≤ Nat.max (finsetMaxDepth u) (finsetMaxDepth v) := by
  refine foldr_max_le_of_forall ?_
  intro t ht
  have ht' : t ∈ u ∪' v := Finset.mem_def.2 ht
  rcases mem_funion.1 ht' with hu | hv
  · exact Nat.le_trans (le_finsetMaxDepth_of_mem hu) (Nat.le_max_left _ _)
  · exact Nat.le_trans (le_finsetMaxDepth_of_mem hv) (Nat.le_max_right _ _)

end InfoSys

end DomainTheory.InformationSystems
