/-ai
If the product system entails a finite set v from a finite set u, then A entails the first projection of v from the first projection of u.

A token of the first projection of v comes from a product token of v that meets the first-projection condition, and the first component of the product entailment of that token is the required entailment in A.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkLeftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkRightInsert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

/-- Product entailment of a set projects to component entailment on `fst`. -/
theorem entSet_fst_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    A.EntSet (fstFinset A B u) (fstFinset A B v) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.1 hbot

end InfoSys

end DomainTheory.InformationSystems
