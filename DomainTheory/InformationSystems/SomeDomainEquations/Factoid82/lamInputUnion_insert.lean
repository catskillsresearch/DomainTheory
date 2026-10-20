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

theorem lamInputUnion_insert
    (s : Finset (List (RawLamToken α) × List (RawLamToken α)))
    (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamInputUnion (insert p s) = listToFinset p.1 ∪' lamInputUnion s := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamInputUnion).1 ht with ⟨q, hq, ht'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact mem_funion.2 (Or.inl ht')
    · exact mem_funion.2 (Or.inr ((mem_lamInputUnion).2 ⟨q, hq, ht'⟩))
  · intro ht
    rcases mem_funion.1 ht with ht | ht
    · exact (mem_lamInputUnion).2 ⟨p, Finset.mem_insert_self p s, ht⟩
    · rcases (mem_lamInputUnion).1 ht with ⟨q, hq, ht'⟩
      exact (mem_lamInputUnion).2 ⟨q, Finset.mem_insert_of_mem hq, ht'⟩

end InfoSys

end DomainTheory.InformationSystems
