/-ai
The intersection map capMap is a computable map from the product of the presentation PNpres with itself to PNpres. The test reduces to the computable inclusion of neighbourhoods, applied twice and conjoined.

The presentation supplies a recursively decidable test of neighbourhood inclusion. Pairing the first, respectively the second, component of the input index with the output index is primitive recursive. The conjunction of the inclusion test along those two reindexings decides the relation of capMap, by capMap_rel_iff after simplifying the unpairing, and passing to the recursively enumerable reading gives computability of the map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.capMap_rel_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **`λx,y. x∩y` is computable.** Reduces to `PNpres.incl_computable`, tested twice and
conjoined. -/
theorem capMap_isComputable :
    ComputableMap (prodPresentation PNpres PNpres) PNpres capMap := by
  constructor
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hr0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  have hr1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) ((hincl.comp hr0).and (hincl.comp hr1))).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact capMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

end DomainTheory.NeighbourhoodSystems.Exercise723
