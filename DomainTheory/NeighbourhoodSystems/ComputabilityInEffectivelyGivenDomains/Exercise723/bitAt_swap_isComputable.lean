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



































































/-- `(i,m) ↦ bitAt m i = 1`, i.e. `m.testBit i`, as a `RecDecidable₂` relation (argument order
swapped from `bitAt`'s own `(n,k) ↦ bitAt n k`, to feed `RecDecidable₂.bForallList`). -/
theorem bitAt_swap_isComputable : RecDecidable₂ (fun i m => bitAt m i = 1) :=
  ⟨fun t => bitAt t.unpair.2 t.unpair.1,
    (primrec_bitAt.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd],
    fun _ => Iff.rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
