module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Data.Set.Lattice.Indexed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def seqFun (u x : Pomega) : Pomega :=
  ⋃ i ∈ x, funOf u (ofNat i)

def seqFunLt (u x : Pomega) (n : ℕ) : Pomega :=
  ⋃ i ∈ x, ⋃ _ : i < n, funOf u (ofNat i)

theorem mem_seqFunLt {u x : Pomega} {n k : ℕ} :
    k ∈ seqFunLt u x n ↔ ∃ i ∈ x, i < n ∧ k ∈ funOf u (ofNat i) := by
  constructor
  · intro hk
    obtain ⟨i, hi, hrest⟩ := Set.mem_iUnion₂.mp hk
    obtain ⟨hlt, hki⟩ := Set.mem_iUnion.mp hrest
    exact ⟨i, hi, hlt, hki⟩
  · intro ⟨i, hi, hlt, hki⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_iUnion.mpr ⟨hlt, hki⟩⟩

def seqCons (x xs : Pomega) : Pomega :=
  graph (fun z => condSet z x (funOf xs (predSet z)))

namespace seqCons

theorem body (x xs : Pomega) :
    IsScottContinuous (fun z => condSet z x (funOf xs (predSet z))) :=
  theorem_1_3.tuple
    (fun _ => condSet.isScottContinuous_left x _)
    (fun z => condSet.isScottContinuous_right z x)
    id_isScottContinuous
    (theorem_1_3 (funOf.isScottContinuous xs) predSet.isScottContinuous)

end seqCons

def seq2 (x y : Pomega) : Pomega :=
  graph (fun z => condSet z x (condSet (predSet z) y botElem))

namespace seq2

theorem body_isScottContinuous (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x (condSet (predSet z) y botElem)) := by
  constructor
  intro z
  have H := theorem_1_3.diag (x := z)
    (f := fun z w => condSet z x (condSet (predSet w) y botElem))
    (fun _w => condSet.isScottContinuous_left x _)
    (fun _z =>
      theorem_1_3 (condSet.isScottContinuous_right _z x)
        (theorem_1_3 (condSet.isScottContinuous_left y botElem)
          predSet.isScottContinuous))
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} := by
      rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this

theorem app (x y z : Pomega) :
    funOf (seq2 x y) z = condSet z x (condSet (predSet z) y botElem) :=
  beta (seq2.body_isScottContinuous x y) z

theorem one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y := by
  rw [app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

theorem zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x := by
  rw [app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

theorem tag_ne (x y : Pomega) :
    seq2 (ofNat 0) x ≠ seq2 (ofNat 1) y := by
  intro h
  have hfun := congrArg (fun w => funOf w (ofNat 0)) h
  have hx : (0 : ℕ) ∈ funOf (seq2 (ofNat 0) x) (ofNat 0) :=
    ⟨1, fun k hk =>
      match k, hk with
      | 0, _ => rfl
      | k + 1, hk =>
        False.elim (Bool.false_ne_true
          (((Nat.testBit_succ 1 k).trans (Nat.zero_testBit k)).symm.trans hk)),
      ⟨1, 0, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hy : (0 : ℕ) ∉ funOf (seq2 (ofNat 1) y) (ofNat 0) := by
    intro ⟨k, hk, hp⟩
    rcases hp with ⟨k', m, heq, hm⟩
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    rcases hm with ⟨h1, _⟩ | ⟨_, ⟨t, ht⟩⟩
    · exact Nat.zero_ne_one h1
    · exact Nat.succ_ne_zero t (hk ht)
  exact hy (hfun ▸ hx)

end seq2

theorem eq_2_22 (x xs z : Pomega) :
    funOf (seqCons x xs) z = condSet z x (funOf xs (predSet z)) :=
  beta (seqCons.body x xs) z

theorem eq_2_23_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x :=
  seq2.zero x y

theorem eq_2_23_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y :=
  seq2.one x y

theorem eq_2_23_ge (x y : Pomega) (n : ℕ) :
    funOf (seq2 x y) (ofNat (n + 2)) = botElem := by
  rw [seq2.app]
  ext k
  simp [condSet, predSet, ofNat, botElem]

namespace seqFun

theorem eq_iUnion_lt (u z : Pomega) :
    seqFun u z = ⋃ n, seqFunLt u z n := by
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    exact Set.mem_iUnion.mpr ⟨i + 1, (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_succ_self i, hki⟩⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    obtain ⟨i, hi, _, hki⟩ := (mem_seqFunLt).mp hn
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hki⟩

theorem left_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun u => seqFun u x) := by
  constructor
  intro u
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    have : k ∈ scottUnion (fun v => funOf v (ofNat i)) u := by
      rw [← (funOf.isScottContinuous_left (ofNat i)).out u]; exact hki
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, Set.mem_iUnion₂.mpr ⟨i, hi, hkn⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨i, hi,
      IsScottContinuous.monotone (funOf.isScottContinuous_left (ofNat i)) hn hki⟩

theorem right_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => seqFun u x) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ i, by simp [e.pow2, Set.singleton_subset_iff, hi],
      Set.mem_iUnion₂.mpr ⟨i, by simp [e.pow2], hki⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨i, hn hi, hki⟩

end seqFun

def seqShift (u : Pomega) : Pomega :=
  graph (fun z => seqFun u (succSet z))

namespace seqShift

theorem isScottContinuous (u : Pomega) :
    IsScottContinuous (fun z => seqFun u (succSet z)) :=
  theorem_1_3 (seqFun.right_isScottContinuous u) succSet.isScottContinuous

theorem app (u z : Pomega) :
    funOf (seqShift u) z = seqFun u (succSet z) :=
  beta (seqShift.isScottContinuous u) z

theorem left_isScottContinuous : IsScottContinuous seqShift :=
  graph_const_isScottContinuous (fun u z => seqFun u (succSet z))
    (fun z => seqFun.left_isScottContinuous (succSet z))

theorem ofNat (u : Pomega) (i : ℕ) :
    funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [seqShift.app]
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
    simp [succSet] at hj; subst hj; exact hmj
  · intro hm
    exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩

end seqShift

def termShift (u : Pomega) : Pomega :=
  graph (fun t => funOf u (succSet t))

namespace termShift

theorem isScottContinuous (u : Pomega) :
    IsScottContinuous (fun t => funOf u (succSet t)) :=
  theorem_1_3 (funOf.isScottContinuous u) succSet.isScottContinuous

theorem app (u t : Pomega) :
    funOf (termShift u) t = funOf u (succSet t) :=
  beta (termShift.isScottContinuous u) t

theorem left_isScottContinuous : IsScottContinuous termShift :=
  graph_const_isScottContinuous (fun u t => funOf u (succSet t))
    (fun t => funOf.isScottContinuous_left (succSet t))

theorem ofNat (u : Pomega) (i : ℕ) :
    funOf (termShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [termShift.app, succSet.ofNat]

end termShift

namespace seqFunLt

theorem succ (u z : Pomega) (n : ℕ) :
    condSet z (funOf u (ofNat 0)) (seqFunLt (seqShift u) (predSet z) n) =
      seqFunLt u z (n + 1) := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0z⟩ | ⟨hpos, t, ht⟩
    · exact (mem_seqFunLt).mpr ⟨0, h0z, Nat.succ_pos n, hk0⟩
    · obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hpos
      refine (mem_seqFunLt).mpr ⟨i + 1, hi, Nat.succ_lt_succ hlt, ?_⟩
      simpa [seqShift.ofNat] using hki
  · intro hk
    obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_of_succ_lt_succ hlt, ?_⟩
      simpa [seqShift.ofNat] using hki

theorem term (u z : Pomega) (n : ℕ) :
    condSet z (funOf u (ofNat 0)) (seqFunLt (termShift u) (predSet z) n) =
      seqFunLt u z (n + 1) := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0z⟩ | ⟨hpos, t, ht⟩
    · exact (mem_seqFunLt).mpr ⟨0, h0z, Nat.succ_pos n, hk0⟩
    · obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hpos
      refine (mem_seqFunLt).mpr ⟨i + 1, hi, Nat.succ_lt_succ hlt, ?_⟩
      simpa [termShift.ofNat] using hki
  · intro hk
    obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_of_succ_lt_succ hlt, ?_⟩
      simpa [termShift.ofNat] using hki

theorem zero (u z : Pomega) : seqFunLt u z 0 = botElem := by
  ext k
  simp [mem_seqFunLt, botElem]

end seqFunLt

end DomainTheory.DataTypesAsLattices
