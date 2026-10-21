/-ai
Forgetting the insertion of a lambda token inserts the underlying raw token into the forget of the remaining set.

By extensionality, a raw token lies in the forget exactly when it is the underlying token of some lambda token of the set. In both directions that lambda token is the inserted token or a member of the remaining set, which is the membership rule for insertion of the underlying token.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamForgetFinset

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem lamForgetFinset_insert (u : Finset (LamToken A)) (p : LamToken A) :
    lamForgetFinset A (insert p u) = insert p.val (lamForgetFinset A u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_lamForgetFinset A).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_lamForgetFinset A).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, rfl⟩
      exact (mem_lamForgetFinset A).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
