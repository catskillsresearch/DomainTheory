/-ai
The first projection of the left lift of a finite set v of tokens of A equals v.

By extensionality, a member of the first projection comes from a token of the lift, hence from the left tag of some member of v, and the projection equation identifies the two tokens. Conversely, the left tag of a member of v lies in the lift and witnesses membership of that token in the first projection.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.mem_liftLeft

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)








theorem fstFinset_liftLeft (v : Finset α) : fstFinset A B (liftLeft A B v) = v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases (mem_liftLeft A B).1 hp with ⟨y, hy, hp'⟩
    subst hp'
    exact (show y = x from hx').symm ▸ hy
  · intro hx
    exact (mem_fstFinset A B).2
      ⟨mkLeft A B x, (mem_liftLeft A B).2 ⟨x, hx, rfl⟩, rfl, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
