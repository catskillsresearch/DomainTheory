module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_plusStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusStep_iter_spec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


theorem primrec_plusIdx : Nat.Primrec (fun t => plusIdx t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 0 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => plusStep w.unpair.2.unpair.2) :=
    primrec_plusStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair Nat.Primrec.left))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  exact (plusStep_iter_spec t.unpair.1 t.unpair.2 t.unpair.1).2.2.2

end DomainTheory.NeighbourhoodSystems.Exercise723
