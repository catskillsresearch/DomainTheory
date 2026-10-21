/-ai
The step plusStep is primitive recursive.

The four components of the packed state are primitive recursive. The bitAt test of the n component at the counter is primitive recursive, and the shift of the m component by the counter is primitive recursive because a left shift is multiplication by a power of two. Selecting that shift or zero, disjoining the result with the accumulator, and packing the unchanged n and m with the incremented counter and the new accumulator is identified with plusStep.
ai-/
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


theorem primrec_plusStep : Nat.Primrec plusStep := by
  have hn : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hm : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have ha : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hbit : Nat.Primrec (fun s : ℕ => bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1) :=
    (primrec_bitAt.comp (hn.pair ha)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hshift : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) := by
    have := primrec_mul₂ hm (primrec_two_pow ha)
    exact this.of_eq fun s => by rw [Nat.shiftLeft_eq]
  have hsel := primrec_selectFn hbit hshift (Nat.Primrec.const 0)
  have hlor : Nat.Primrec (fun s : ℕ => myLor s.unpair.2.unpair.2
      (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
        (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0)) :=
    (primrec_myLor.comp (hacc.pair hsel)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact ((hn.pair hm).pair ((primrec_add₂ ha (Nat.Primrec.const 1)).pair hlor)).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
