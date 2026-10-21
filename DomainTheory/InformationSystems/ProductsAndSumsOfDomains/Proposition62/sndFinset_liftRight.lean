/-ai
The second projection of the right lift of a finite set w of tokens of B equals w.

By extensionality, a member of the second projection comes from a token of the lift, hence from the right tag of some member of w, and the projection equation identifies the two tokens. Conversely, the right tag of a member of w lies in the lift and witnesses membership of that token in the second projection.
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


theorem sndFinset_liftRight (w : Finset β) : sndFinset A B (liftRight A B w) = w := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases (mem_liftRight A B).1 hp with ⟨z, hz, hp'⟩
    subst hp'
    exact (show z = y from hy').symm ▸ hz
  · intro hy
    exact (mem_sndFinset A B).2
      ⟨mkRight A B y, (mem_liftRight A B).2 ⟨y, hy, rfl⟩, rfl, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
