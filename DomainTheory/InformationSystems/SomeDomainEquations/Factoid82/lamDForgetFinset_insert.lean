module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamDForgetFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamDForgetFinset_insert (u : Finset (LamDToken A)) (p : LamDToken A) :
    lamDForgetFinset A (insert p u) = insert p.val (lamDForgetFinset A u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_lamDForgetFinset A).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_lamDForgetFinset A).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, rfl⟩
      exact (mem_lamDForgetFinset A).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
