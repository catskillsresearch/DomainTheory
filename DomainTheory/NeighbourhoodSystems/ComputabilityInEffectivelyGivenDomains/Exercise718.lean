module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectivelyIsomorphic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.toDomainIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.iterIterEffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2_of_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.exists_inner_bound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.pair_lt_pair_of_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_comp_Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_comp_Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_iterEnum_iter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.masterIdx_iterPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel_enum_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel_enum_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_isComputable

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}


namespace EffectiveIso

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}


end EffectiveIso

/-- **Exercise 7.18 — effective isomorphism implies domain isomorphism.** -/
theorem EffectivelyIsomorphic.isomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {P : ComputablePresentation V} {Q : ComputablePresentation W}
    (h : EffectivelyIsomorphic P Q) : V ≅ᴰ W :=
  h.elim fun e => ⟨e.toDomainIso⟩

variable {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)


variable {P}


/-- **Exercise 7.18 (Scott 1981, PRG-19).** If `D` is effectively given then `D^∞ ≅ (D^∞)^∞` is
effective. -/
theorem iterSys_effectivelyIsomorphic_iterIter (P : ComputablePresentation V) :
    EffectivelyIsomorphic (iterPresentation P) (iterPresentation (iterPresentation P)) :=
  ⟨iterIterEffectiveIso P⟩

/-- As a corollary, `D^∞ ≅ (D^∞)^∞` as domains (Scott's underlying isomorphism). -/
theorem iterSys_isomorphic_iterIter (P : ComputablePresentation V) :
    iterSys V ≅ᴰ iterSys (iterSys V) :=
  (iterSys_effectivelyIsomorphic_iterIter P).isomorphic

end Exercise718
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems.Exercise718

set_option linter.unusedVariables false

theorem example_718.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V),
  @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic (Prod Nat α) (Prod Nat (Prod Nat α))
    (@DomainTheory.NeighbourhoodSystems.iterSys α V)
    (@DomainTheory.NeighbourhoodSystems.iterSys (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (@DomainTheory.NeighbourhoodSystems.iterPresentation α V P)
    (@DomainTheory.NeighbourhoodSystems.iterPresentation (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
      (@DomainTheory.NeighbourhoodSystems.iterPresentation α V P)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise718.iterSys_effectivelyIsomorphic_iterIter

end DomainTheory.NeighbourhoodSystems.Exercise718
