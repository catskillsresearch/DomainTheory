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

theorem finsetMaxDepth_insert_le (u : Finset (RawLamToken α)) (a : RawLamToken α) :
    finsetMaxDepth (insert a u) ≤ Nat.max (rawDepth a) (finsetMaxDepth u) := by
  refine foldr_max_le_of_forall ?_
  intro x hx
  have hx' : x ∈ insert a u := Finset.mem_def.2 hx
  rcases Finset.mem_insert.mp hx' with rfl | hu
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans (le_finsetMaxDepth_of_mem hu) (Nat.le_max_right _ _)

end InfoSys

end DomainTheory.InformationSystems
