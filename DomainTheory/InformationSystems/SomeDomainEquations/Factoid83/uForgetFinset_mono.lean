/-ai
The forget-finset is monotone: if v is contained in u, then the forget-finset of v is contained in the forget-finset of u.

A token in the smaller forget-finset is the value of some member of v, hence of u, so the membership criterion places it in the larger forget-finset.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_uForgetFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

theorem uForgetFinset_mono {u v : Finset UToken} (h : v ⊆ u) :
    uForgetFinset v ⊆ uForgetFinset u := by
  intro t ht
  rcases (mem_uForgetFinset).1 ht with ⟨p, hp, rfl⟩
  exact (mem_uForgetFinset).2 ⟨p, h hp, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
