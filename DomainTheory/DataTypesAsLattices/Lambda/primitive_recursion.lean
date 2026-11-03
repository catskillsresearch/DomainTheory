module

public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.distributive_functions
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def primRecStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2 (.lam 3
    (.cond (.var 3) (.var 0)
      (.app (.app (.var 1) (.pred (.var 3)))
        (.app (.var 2) (.pred (.var 3))))))))

namespace primRecStepTerm

theorem interp (a f u n : Pomega) :
    funOf (funOf (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f) u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) := by
  change funOf (funOf (funOf (funOf (DomainTheory.DataTypesAsLattices.interp (Term.lam 0 _) (fun _ => botElem)) a) f) u) n = _
  rw [theorem_2_2.beta]
  rw [theorem_2_2.beta]
  rw [theorem_2_2.beta]
  rw [theorem_2_2.beta]
  simp [_root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update]

end primRecStepTerm

def primRecStep (a f u : Pomega) : Pomega :=
  graph (fun n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))

namespace primRecStep

theorem body_isScottContinuous_n (a f u : Pomega) :
    IsScottContinuous (fun n =>
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n)))) :=
  theorem_1_3.tuple
    (fun y => condSet.isScottContinuous_left a y)
    (fun n => condSet.isScottContinuous_right n a)
    id_isScottContinuous
    (theorem_1_3.tuple
      (fun y => funOf.isScottContinuous_left y)
      (fun x => funOf.isScottContinuous x)
      (theorem_1_3 (funOf.isScottContinuous f) predSet.isScottContinuous)
      (theorem_1_3 (funOf.isScottContinuous u) predSet.isScottContinuous))

theorem graph_of (a f : Pomega) :
    graph (primRecStep a f) =
      funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f := by
  change graph (primRecStep a f) =
    funOf (funOf (DomainTheory.DataTypesAsLattices.interp (Term.lam 0 (.lam 1 (.lam 2 (.lam 3
      (.cond (.var 3) (.var 0)
        (.app (.app (.var 1) (.pred (.var 3)))
          (.app (.var 2) (.pred (.var 3))))))))) (fun _ => botElem)) a) f
  rw [theorem_2_2.beta, theorem_2_2.beta]
  apply congrArg graph
  funext u
  apply congrArg graph
  funext n
  simp [DomainTheory.DataTypesAsLattices.interp, envSet, Function.update]

theorem isScottContinuous (a f : Pomega) :
    IsScottContinuous (primRecStep a f) :=
  graph_const_isScottContinuous
    (fun u n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))
    (fun n => theorem_1_3 (condSet.isScottContinuous_right n a)
      (theorem_1_3 (funOf.isScottContinuous (funOf f (predSet n)))
        (funOf.isScottContinuous_left (predSet n))))

theorem app (a f u n : Pomega) :
    funOf (primRecStep a f u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) :=
  beta (primRecStep.body_isScottContinuous_n a f u) n

end primRecStep

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

def primRecHat (a f x : Pomega) : Pomega :=
  ⋃ n ∈ x, primRecVal a f n

namespace primRecHat

theorem zero (a f : Pomega) : primRecHat a f (ofNat 0) = a := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    subst hn; simpa [primRecVal] using hkn
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨0, rfl, hk⟩

theorem ofNat (a f : Pomega) : ∀ n,
    primRecHat a f (ofNat n) = primRecVal a f n
  | 0 => primRecHat.zero a f
  | n + 1 => by
    ext k
    constructor
    · intro hk
      obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
      subst hm; simpa [primRecVal] using hkm
    · intro hk
      exact Set.mem_iUnion₂.mpr ⟨n + 1, rfl, hk⟩

end primRecHat

theorem eq_2_27 (a f x : Pomega) :
    primRecHat a f x = funOf (funOf dollarC (fix (primRecStep a f))) x := by
  rw [eq_2_25]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal.fix] using hkn
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal.fix] using hkn

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def precTerm : Term :=
  .lam 0
    (.app
      (.app
        (.app (.var 3) (.app (.var 4) (.app (.var 6) (.var 0))))
        (.lam 1 (.lam 2
          (.app (.var 5)
            (.app (.app (.var 8) (.app (.var 6) (.var 0)))
              (.app (.app (.var 8) (.var 1)) (.var 2)))))))
      (.app (.var 7) (.var 0)))

end DomainTheory.DataTypesAsLattices
