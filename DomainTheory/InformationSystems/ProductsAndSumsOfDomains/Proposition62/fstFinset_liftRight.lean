/-ai
The first projection of the right lift of a finite set of tokens of B is contained in the singleton of the bottom token of A.

A member of that first projection comes from a right-tagged token of the lift, and the projection equation forces the member to be the bottom token of A.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.mem_liftRight

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)








theorem fstFinset_liftRight (w : Finset β) :
    fstFinset A B (liftRight A B w) ⊆ ({A.bot} : Finset α) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
  rcases (mem_liftRight A B).1 hp with ⟨y, _, hp'⟩
  subst hp'
  have : x = A.bot := hx'.symm
  exact Finset.mem_singleton.mpr this

end InfoSys
end DomainTheory.InformationSystems
