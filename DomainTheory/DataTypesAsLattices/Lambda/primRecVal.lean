module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStep
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def primRecVal (a f : Pomega) : ℕ → Pomega
  | 0 => a
  | n + 1 => funOf (funOf f (ofNat n)) (primRecVal a f n)

namespace primRecVal

theorem fix (a f : Pomega) : ∀ n,
    funOf (DomainTheory.DataTypesAsLattices.fix (primRecStep a f)) (ofNat n) =
      primRecVal a f n
  | 0 => by
    have hfix := (theorem_1_4 (primRecStep.isScottContinuous a f)).1
    calc funOf (DomainTheory.DataTypesAsLattices.fix (primRecStep a f)) (ofNat 0)
        = funOf (primRecStep a f
            (DomainTheory.DataTypesAsLattices.fix (primRecStep a f))) (ofNat 0) := by
          rw [hfix]
      _ = condSet (ofNat 0) a
            (funOf (funOf f (predSet (ofNat 0)))
              (funOf (DomainTheory.DataTypesAsLattices.fix (primRecStep a f))
                (predSet (ofNat 0)))) :=
          primRecStep.app a f _ _
      _ = a := eq_2_7_zero _ _
  | n + 1 => by
    have hfix := (theorem_1_4 (primRecStep.isScottContinuous a f)).1
    calc funOf (DomainTheory.DataTypesAsLattices.fix (primRecStep a f)) (ofNat (n + 1))
        = funOf (primRecStep a f
            (DomainTheory.DataTypesAsLattices.fix (primRecStep a f))) (ofNat (n + 1)) := by
          rw [hfix]
      _ = condSet (ofNat (n + 1)) a
            (funOf (funOf f (predSet (ofNat (n + 1))))
              (funOf (DomainTheory.DataTypesAsLattices.fix (primRecStep a f))
                (predSet (ofNat (n + 1))))) :=
          primRecStep.app a f _ _
      _ = funOf (funOf f (ofNat n))
            (funOf (DomainTheory.DataTypesAsLattices.fix (primRecStep a f)) (ofNat n)) := by
          rw [eq_2_7_succ, predSet.ofNat_succ]
      _ = funOf (funOf f (ofNat n)) (primRecVal a f n) := by
          rw [«fix» a f n]

end primRecVal

end DomainTheory.DataTypesAsLattices
