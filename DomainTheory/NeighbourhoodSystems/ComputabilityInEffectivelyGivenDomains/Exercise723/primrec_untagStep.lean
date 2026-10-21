/-ai
The transition untagStep is primitive recursive.

The done flag, the reversed accumulator, and the carried value are primitive-recursive projections, as are the two components of unnum of the code and the zero test of the first. The halt branch pairs the second component with the flag one, the reversed accumulator, and that second component. The continuation pairs it with the flag zero, the successor of the pairing of the predecessor of the first component with the reversed accumulator, and the carried value. Selection on the zero test, then selection of the identity against that inner branch on the done flag, is primitive recursive and equals untagStep by reflexivity.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_unnum1
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_unnum2

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)






























































theorem primrec_untagStep : Nat.Primrec untagStep := by
  have hdone : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hrevAcc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have ha : Nat.Primrec (fun w : ℕ => unnum1 w.unpair.1) := primrec_unnum1.comp Nat.Primrec.left
  have hb : Nat.Primrec (fun w : ℕ => unnum2 w.unpair.1) := primrec_unnum2.comp Nat.Primrec.left
  have hz : Nat.Primrec (fun w : ℕ => isZero (unnum1 w.unpair.1)) := primrec_isZero.comp ha
  have hhalt : Nat.Primrec (fun w : ℕ => Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 1 (Nat.pair w.unpair.2.unpair.2.unpair.1 (unnum2 w.unpair.1)))) :=
    hb.pair ((Nat.Primrec.const 1).pair (hrevAcc.pair hb))
  have hcont : Nat.Primrec (fun w : ℕ => Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 0
        (Nat.pair (Nat.pair (unnum1 w.unpair.1 - 1) w.unpair.2.unpair.2.unpair.1 + 1)
          w.unpair.2.unpair.2.unpair.2))) :=
    hb.pair ((Nat.Primrec.const 0).pair
      ((Nat.Primrec.succ.comp ((primrec_sub₂ ha (Nat.Primrec.const 1)).pair hrevAcc)).pair hval))
  have hinner := primrec_selectFn hz hhalt hcont
  exact (primrec_selectFn hdone primrec_id hinner).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
