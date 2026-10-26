module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.filterEnv
public import DomainTheory.DataTypesAsLattices.Enumeration.filterTerm
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import Mathlib.Data.Set.Lattice.Indexed
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Enumeration.beforeHalt
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum
public import DomainTheory.DataTypesAsLattices.Enumeration.filterNum
public import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer
public import DomainTheory.DataTypesAsLattices.Enumeration.filterSeq_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_25
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def filterC : Pomega := interp filterTerm filterEnv

namespace filterC

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem combinatory : IsCombinatory filterC := by
  rw [filterC, theorem_2_4.complete]
  exact ofComb.combinatory _ _ filterEnv.combinatory

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (m : ℕ) :
    funOf filterC (ofNat m) = {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  have hgraph :
      filterC = graph (fun v =>
        predSet (seqFun
          (graph (fun j =>
            funOf filterRealizer (funOf (funOf pairComb v) j)))
          topElem)) := by
    unfold filterC filterTerm
    apply congrArg graph
    funext v
    simp [interp, envSet, Function.update, filterEnv,
      _root_.DomainTheory.DataTypesAsLattices.eq_2_25]
  have hcont : IsScottContinuous fun v =>
      predSet (seqFun
        (graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)))
        topElem) :=
    theorem_1_3 predSet.isScottContinuous
      (theorem_1_3 (seqFun.left_isScottContinuous topElem)
        filterSeq_isScottContinuous)
  have hbody :
      funOf filterC (ofNat m) =
        predSet (seqFun
          (graph (fun j =>
            funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
          topElem) := by
    rw [hgraph]
    exact beta hcont (ofNat m)
  have hseq (i : ℕ) :
      funOf (graph (fun j =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
        (ofNat i) =
        ofNat (filterNum (Nat.pair m i)) := by
    have hβ : funOf (graph (fun j =>
        funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
        (ofNat i) =
        funOf filterRealizer (funOf (funOf pairComb (ofNat m)) (ofNat i)) :=
      beta (theorem_1_3 (funOf.isScottContinuous filterRealizer)
        (funOf.isScottContinuous (funOf pairComb (ofNat m)))) (ofNat i)
    rw [hβ, pairComb.app, filterRealizer.realizes]
  rw [hbody]
  ext j
  constructor
  · intro hj
    have : j + 1 ∈ seqFun
        (graph (fun z =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) z)))
        topElem := hj
    obtain ⟨i, -, hij⟩ := Set.mem_iUnion₂.mp this
    have : filterNum (Nat.pair m i) = j + 1 := by
      have hij' : j + 1 ∈ ofNat (filterNum (Nat.pair m i)) := by
        rwa [← hseq i]
      simpa [ofNat, eq_comm] using hij'
    have hbf : beforeHalt m i := by
      by_contra h
      simp [filterNum, Nat.unpair_pair, h] at this
    have hij' : i = j := by
      simp [filterNum, Nat.unpair_pair, hbf] at this
      omega
    subst hij'
    simpa [beforeHalt, Nat.lt_succ_iff] using hbf
  · intro hj
    have hbf : beforeHalt m j := by
      simpa [beforeHalt, Nat.lt_succ_iff] using hj
    have : filterNum (Nat.pair m j) = j + 1 := by
      simp [filterNum, Nat.unpair_pair, hbf]
    refine (show j + 1 ∈ seqFun
        (graph (fun z =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) z)))
        topElem from ?_)
    refine Set.mem_iUnion₂.mpr ⟨j, Set.mem_univ j, ?_⟩
    have : j + 1 ∈ ofNat (filterNum (Nat.pair m j)) := by
      simp [ofNat, this]
    rwa [← hseq j] at this

end filterC

end DomainTheory.DataTypesAsLattices
