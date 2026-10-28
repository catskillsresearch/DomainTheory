module

public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem
public import DomainTheory.DataTypesAsLattices.Functionality.arrowE
public import DomainTheory.DataTypesAsLattices.Functionality.sumE
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Functionality.mem
public import DomainTheory.DataTypesAsLattices.Lambda.interC
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def sumMed (f g : Pomega) : Pomega :=
  graph (fun u =>
    condSet (funOf u (ofNat 0))
      (funOf f (funOf u (ofNat 1)))
      (funOf g (funOf u (ofNat 1))))

namespace sumMed

theorem body_isScottContinuous (f g : Pomega) :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1)))) :=
  continuous_nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (funOf.isScottContinuous_left (ofNat 0))
    (theorem_1_3 (funOf.isScottContinuous f)
      (funOf.isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf.isScottContinuous g)
      (funOf.isScottContinuous_left (ofNat 1)))

theorem app (f g u : Pomega) :
    funOf (sumMed f g) u =
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1))) :=
  beta (sumMed.body_isScottContinuous f g) u

theorem app_inl (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 0) x) = funOf f x := by
  rw [sumMed.app, pairElem.fst, pairElem.snd, condSet.ofNat_zero]

theorem app_inr (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 1) x) = funOf g x := by
  rw [sumMed.app, pairElem.fst, pairElem.snd, condSet.ofNat_one]

theorem isGraph (f g : Pomega) :
    sumMed f g = graph (fun u => funOf (sumMed f g) u) := by
  apply graph_ext
  intro u
  exact (sumMed.app f g u).symm

theorem rel {A B C : RestrictedEquiv} {f g : Pomega}
    (hf : (arrowE A C).mem f) (hg : (arrowE B C).mem g) :
    (arrowE (sumE A B) C).mem (sumMed f g) := by
  refine ⟨sumMed.isGraph f g, sumMed.isGraph f g, ?_⟩
  intro u v huv
  rcases huv with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
  · have hmu : funOf (sumMed f g) u = funOf f (funOf u (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hu).trans
        (sumMed.app_inl f g _)
    have hmv : funOf (sumMed f g) v = funOf f (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed.app_inl f g _)
    rw [hmu, hmv]
    exact hf.2.2 (funOf u (ofNat 1)) (funOf v (ofNat 1)) hA
  · have hmu : funOf (sumMed f g) u = funOf g (funOf u (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hu).trans
        (sumMed.app_inr f g _)
    have hmv : funOf (sumMed f g) v = funOf g (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed.app_inr f g _)
    rw [hmu, hmv]
    exact hg.2.2 (funOf u (ofNat 1)) (funOf v (ofNat 1)) hB

theorem rel_unique {A B C : RestrictedEquiv} {f g h : Pomega}
    (hh : (arrowE (sumE A B) C).mem h)
    (hinl : ∀ x y, A.rel x y →
      C.rel (funOf h (pairElem (ofNat 0) x)) (funOf f y))
    (hinr : ∀ x y, B.rel x y →
      C.rel (funOf h (pairElem (ofNat 1) x)) (funOf g y)) :
    (arrowE (sumE A B) C).rel h (sumMed f g) := by
  refine ⟨hh.1, sumMed.isGraph f g, ?_⟩
  intro u v huv
  rcases huv with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
  · have hhu :
        funOf h u = funOf h (pairElem (ofNat 0) (funOf u (ofNat 1))) :=
      congrArg (fun w => funOf h w) hu
    have hmv : funOf (sumMed f g) v = funOf f (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed.app_inl f g _)
    rw [hhu, hmv]
    exact hinl (funOf u (ofNat 1)) (funOf v (ofNat 1)) hA
  · have hhu :
        funOf h u = funOf h (pairElem (ofNat 1) (funOf u (ofNat 1))) :=
      congrArg (fun w => funOf h w) hu
    have hmv : funOf (sumMed f g) v = funOf g (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed.app_inr f g _)
    rw [hhu, hmv]
    exact hinr (funOf u (ofNat 1)) (funOf v (ofNat 1)) hB

end sumMed

end DomainTheory.DataTypesAsLattices
