/-ai
The state iterator untagState is primitive recursive.

The base map, which pairs its argument with the triple of zeros, is primitive recursive by pairing the identity with constant zero. The step, which applies untagStep to the second component of the second component, is primitive recursive by composing the primitive recursiveness of untagStep with two right projections. Primitive recursion of that base and step, composed with the pairing of the identity and successor, agrees with untagState: the unpaired form simplifies, the constant-iteration equation rewrites the recursion, and unfolding untagState leaves the successor iterate.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_untagStep

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)































































theorem primrec_untagState : Nat.Primrec untagState := by
  have hbase : Nat.Primrec (fun c : ℕ => Nat.pair c (Nat.pair (0 : ℕ) (Nat.pair 0 0))) :=
    primrec_id.pair ((Nat.Primrec.const 0).pair ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0)))
  have hstep : Nat.Primrec (fun w : ℕ => untagStep w.unpair.2.unpair.2) :=
    primrec_untagStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine (hprec.comp (primrec_id.pair Nat.Primrec.succ)).of_eq fun c => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  unfold untagState
  rw [Function.iterate_succ_apply']

end DomainTheory.NeighbourhoodSystems.Exercise723
