module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


























theorem plusStep_unpair22 (s : ℕ) : (plusStep s).unpair.2.unpair.2 =
    myLor s.unpair.2.unpair.2 (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
      (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0) := by
  unfold plusStep; rw [unpair_pair_snd, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems.Exercise723
