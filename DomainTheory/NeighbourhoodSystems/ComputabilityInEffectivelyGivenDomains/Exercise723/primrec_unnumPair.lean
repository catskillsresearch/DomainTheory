/-ai
The packed unnumbering unnumPair is primitive recursive.

Primitive recursion starts from the constant packing of 0 with 0 and steps by nextCellStep on the accumulator, with the iteration count equal to the input. The constant-iterator form of that recursion is identified with unnumPair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_nextCellStep

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)























































theorem primrec_unnumPair : Nat.Primrec unnumPair := by
  have hbase : Nat.Primrec (fun _ : ℕ => Nat.pair (0 : ℕ) 0) := Nat.Primrec.const (Nat.pair 0 0)
  have hstep : Nat.Primrec (fun w : ℕ => nextCellStep w.unpair.2.unpair.2) :=
    primrec_nextCellStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine (hprec.comp ((Nat.Primrec.const 0).pair primrec_id)).of_eq fun v => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  show Nat.rec (Nat.pair 0 0) (fun _ ih => nextCellStep ih) v = unnumPair v
  rw [rec_const_iterate]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
