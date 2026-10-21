/-ai
The effective isomorphism between the iterated presentation of a computable presentation and the iteration of that iterated presentation has forward map the reindexing from the iteration to the double iteration and inverse map the reindexing in the other direction. Both maps are computable, and the two composite laws are the mutual inverse laws of those reindexings.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_comp_Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_comp_Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_isComputable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

variable {P}

/-- **Exercise 7.18 (Scott 1981, PRG-19) — `D^∞ ≅ (D^∞)^∞` is an *effective* isomorphism.** Relative
to `iterPresentation P` and `iterPresentation (iterPresentation P)`, the reindexing maps `F`, `G` are
mutually inverse computable approximable maps. -/
def iterIterEffectiveIso (P : ComputablePresentation V) :
    EffectiveIso (iterPresentation P) (iterPresentation (iterPresentation P)) where
  toMap := Fmap V
  invMap := Gmap V
  toMap_computable := Fmap_isComputable
  invMap_computable := Gmap_isComputable
  left_inv := Gmap_comp_Fmap
  right_inv := Fmap_comp_Gmap

end Exercise718

end DomainTheory.NeighbourhoodSystems
