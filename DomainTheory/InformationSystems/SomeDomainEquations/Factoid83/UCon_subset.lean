/-ai
A subset of a consistent finite set of U-tokens is consistent.

A V-entailment of top from the forget-image of the subset would, by monotonicity of V-entailment along the inclusion of forget-images, be a V-entailment of top from the larger forget-image, contradicting consistency of the larger set.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UCon

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem UCon_subset {u v : Finset UToken}
    (hu : UCon u) (hv : v ⊆ u) : UCon v :=
  fun h => hu (VEnt_mono (uForgetFinset_mono hv) h)

end InfoSys

end DomainTheory.InformationSystems
