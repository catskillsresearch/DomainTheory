/-ai
The right projection of the left sum lift of a finite set of tokens of A is empty.

By extensionality, a member of the right projection would be a token of the lift equal to a right constructor, which the membership characterization of the left lift excludes, and the empty set contributes no members.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumLeft

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

theorem rhtFinset_liftSumLeft (v : Finset α) :
    rhtFinset (liftSumLeft (β := β) v) = ∅ := by
  ext y
  constructor
  · intro hy
    rcases (mem_liftSumLeft (β := β)).1 ((mem_rhtFinset).1 hy) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

end InfoSys

end DomainTheory.InformationSystems
