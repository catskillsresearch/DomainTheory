/-ai
Applying filterC to the numeral of m yields the set of j such that the shifted halting enumerator differs from m at every index up to j.

Unfold filterC and filterTerm. Simplifying the interpretation in filterEnv by equation 2.25 shows that filterC is the graph of the predecessor of the sequence, taken at the top element, of the graph of the map sending an index to the filter realizer applied to the pairing combinator at the argument and that index. Theorem 1.3 gives Scott continuity of this body, from continuity of the predecessor, continuity of sequencing on the left at the top element, and continuity of the filter sequence, so the beta law computes the application at the numeral of m. A second beta law, from continuity of application of the filter realizer and of the pairing combinator, together with the pairing law and the fact that the filter realizer realizes filterNum, identifies the sequence value at the numeral of i with the numeral of filterNum on the pair of m and i. Extensionality then splits in two directions. If j lies in the predecessor, then j + 1 lies in the sequence, so some i has filterNum of the pair of m and i equal to j + 1. Failure of beforeHalt on that pair would make the value 0, so beforeHalt holds, and the same computation forces i = j, which is the enumerator condition up to j. Conversely, the enumerator condition gives beforeHalt at m and j, so filterNum of that pair is j + 1, and j + 1 lies in the sequence at the index j.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer_realizes
public import DomainTheory.DataTypesAsLattices.Enumeration.filterSeq_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem filterC_app (m : ℕ) :
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
    simp [interp, envSet, Function.update, filterEnv, eq_2_25]
  have hcont : IsScottContinuous fun v =>
      predSet (seqFun
        (graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)))
        topElem) :=
    theorem_1_3 predSet_isScottContinuous
      (theorem_1_3 (seqFun_left_isScottContinuous topElem)
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
      beta (theorem_1_3 (funOf_isScottContinuous filterRealizer)
        (funOf_isScottContinuous (funOf pairComb (ofNat m)))) (ofNat i)
    rw [hβ, pairComb_app, filterRealizer_realizes]
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

end DomainTheory.DataTypesAsLattices
