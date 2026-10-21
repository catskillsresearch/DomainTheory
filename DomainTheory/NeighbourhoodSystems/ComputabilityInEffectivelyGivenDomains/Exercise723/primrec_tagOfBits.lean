/-ai
The map sending a paired number to tagOfBits of its two components is primitive recursive.

The bit code of the left component against itself is primitive recursive. Applying tagCode to that code paired with the right component is identified with tagOfBits after simplifying the unpairing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_tagCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)




















































theorem primrec_tagOfBits : Nat.Primrec (fun t => tagOfBits t.unpair.1 t.unpair.2) := by
  have hj : Nat.Primrec (fun t : ℕ => bitsCode t.unpair.1 t.unpair.1) :=
    (primrec_bitsCode.comp (Nat.Primrec.left.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_tagCode.comp (hj.pair Nat.Primrec.right)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
