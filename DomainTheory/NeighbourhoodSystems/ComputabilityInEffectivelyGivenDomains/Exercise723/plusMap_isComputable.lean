/-ai
The Minkowski-sum map plusMap is a computable map from the product presentation of PNpres to PNpres. The test reduces to one computable neighbourhood inclusion against the primitive-recursive reindexing plusIdx.

The presentation supplies a recursively decidable inclusion test. Pairing the two input indices and then applying plusIdx is primitive recursive, and pairing the result with the output index is primitive recursive. The inclusion test along that reindexing decides the relation of plusMap, by plusMap_rel_iff after simplifying the unpairing, and the recursively enumerable reading is computability of the map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_plusIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusMap_rel_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **`λx,y. x+y` is computable.** Reduces to `PNpres.incl_computable` against the primitive
recursive reindexing `plusIdx`. -/
theorem plusMap_isComputable :
    ComputableMap (prodPresentation PNpres PNpres) PNpres plusMap := by
  constructor
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hpair : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.left)
  have hplus : Nat.Primrec (fun t : ℕ => plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (primrec_plusIdx.comp hpair).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hr : Nat.Primrec (fun t => Nat.pair (plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2)
      t.unpair.2) := hplus.pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact plusMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

end DomainTheory.NeighbourhoodSystems.Exercise723
