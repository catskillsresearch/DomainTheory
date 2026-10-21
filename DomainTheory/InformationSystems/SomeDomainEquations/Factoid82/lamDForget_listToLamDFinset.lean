/-ai
If every token of a list of raw lambda tokens is well formed, then forgetting the finite set of depth tokens read from the list recovers the finite set of the list.

By extensionality, a forgotten token is the underlying token of a depth token of that set, hence a member of the list. Conversely a list member packages as a depth token by the given well-formedness, and forgetting it returns the member.
ai-/
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamWF
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_listToLamDFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamDForget_listToLamDFinset (xs : List (RawLamToken α))
    (h : ∀ t ∈ xs, IsLamWF A t) :
    lamDForgetFinset A (listToLamDFinset A xs h) = listToFinset xs := by
  ext t
  rw [mem_lamDForgetFinset, mem_listToFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_listToLamDFinset A).1 hp
  · intro ht
    let p : LamDToken A := ⟨t, h t ht⟩
    exact ⟨p, (mem_listToLamDFinset A).2 ht, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
