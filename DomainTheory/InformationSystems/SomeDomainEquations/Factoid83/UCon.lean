module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.not_VEnt_singleton_ne_top

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

def UCon (u : Finset UToken) : Prop :=
  ¬ VEnt (uForgetFinset u) .top

theorem UCon.singleton (p : UToken) : UCon {p} := by
  rw [UCon, uForgetFinset.singleton]
  exact not_VEnt_singleton_ne_top p.property.out

theorem UCon.subset {u v : Finset UToken}
    (hu : UCon u) (hv : v ⊆ u) : UCon v :=
  fun h => hu (VEnt_mono (uForgetFinset.mono hv) h)

end InfoSys

end DomainTheory.InformationSystems
