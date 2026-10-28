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

theorem sndFinset_liftLeft (v : Finset α) :
    sndFinset A B (liftLeft A B v) ⊆ ({B.bot} : Finset β) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  rcases (mem_liftLeft A B).1 hp with ⟨x, _, hp'⟩
  subst hp'

  have : y = B.bot := hy'.symm
  exact Finset.mem_singleton.mpr this

end InfoSys
end DomainTheory.InformationSystems
