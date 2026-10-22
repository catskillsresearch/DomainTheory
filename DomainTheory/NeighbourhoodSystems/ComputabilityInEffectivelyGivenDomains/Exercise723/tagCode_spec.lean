
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tag_eq_foldl_reverse

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


theorem tagCode_spec (code m : ℕ) : tagCode code m = tag (decodeList code) m := by
  unfold tagCode
  rw [foldCode_eq']
  have hstep : (fun acc x => tagStep (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => num (x + 1) acc) := by
    funext acc x
    show tagStep (Nat.pair x (Nat.pair acc 0)) = num (x + 1) acc
    unfold tagStep
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeList_appendCode, decodeList_zero, List.append_nil]
  exact (tag_eq_foldl_reverse (decodeList code) m).symm

end DomainTheory.NeighbourhoodSystems.Exercise723
