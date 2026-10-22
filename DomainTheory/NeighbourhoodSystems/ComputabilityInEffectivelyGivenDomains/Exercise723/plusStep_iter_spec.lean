module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusStep_unpair11
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusStep_unpair12
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusStep_unpair21
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusStep_unpair22

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


theorem plusStep_iter_spec (n m : ℕ) (k : ℕ) :
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.1 = n ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.2 = m ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.1 = k ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.2 = orUpTo n m k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.iterate_zero, id_eq, unpair_pair_fst, unpair_pair_snd, orUpTo]
  | succ k ih =>
    obtain ⟨hn, hm, ha, hacc⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [plusStep_unpair11, hn]
    · rw [plusStep_unpair12, hm]
    · rw [plusStep_unpair21, ha]
    · rw [plusStep_unpair22, hn, hm, ha, hacc]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
