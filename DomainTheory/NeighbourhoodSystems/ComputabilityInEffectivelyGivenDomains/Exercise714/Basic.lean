module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714.tFun
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714.tFun

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise714

open NeighborhoodSystem Domain.Recursive DomainTheory.NeighbourhoodSystems

/-- **A non-empty recursively enumerable set is the range of a primitive recursive function.** This
is the precise content of Scott's prose after Definition 7.2 (*"there is a primitive recursive `r`
with `y = {Y_{r(i)}}`"*). Given a witness `a ∈ p` and the `{0,1}` decider `qc` of the relation `q`
underlying `p` (`p n ↔ ∃ i, q ⟨i,n⟩`), the function `r w := selectFn (isOne (qc w)) w.2 a` enumerates
`p`: on a code `w = ⟨i,n⟩` with `q ⟨i,n⟩` it returns `n`, otherwise it returns the fixed `a`. Its
range is exactly `p` (the fall-back `a` covers the codes that do not witness anything — this is where
non-emptiness is used). -/
theorem repred_exists_primrec_range {p : ℕ → Prop} (hp : REPred p) {a : ℕ} (ha : p a) :
    ∃ r : ℕ → ℕ, Nat.Primrec r ∧ ∀ n, p n ↔ ∃ i, r i = n := by
  obtain ⟨q, ⟨qc, hqcp, hqcs⟩, hqe⟩ := hp
  refine ⟨fun w => selectFn (isOne (qc w)) w.unpair.2 a,
    primrec_selectFn (primrec_isOne.comp hqcp) Nat.Primrec.right (Nat.Primrec.const a), ?_⟩
  -- Every value of the enumerator lies in `p`.
  have hrw_mem : ∀ w, p (selectFn (isOne (qc w)) w.unpair.2 a) := by
    intro w
    rcases (show isOne (qc w) = 0 ∨ isOne (qc w) = 1 by
        have := isOne_le_one (qc w); omega) with h0 | h1
    · rw [h0, selectFn_zero]; exact ha
    · rw [h1, selectFn_one]
      have hqw : q w := (hqcs w).mpr ((isOne_eq_one_iff (qc w)).mp h1)
      rw [hqe w.unpair.2]
      exact ⟨w.unpair.1, by rw [pair_unpair]; exact hqw⟩
  intro n
  constructor
  · intro hpn
    rw [hqe n] at hpn
    obtain ⟨i, hi⟩ := hpn
    refine ⟨Nat.pair i n, ?_⟩
    show selectFn (isOne (qc (Nat.pair i n))) (Nat.pair i n).unpair.2 a = n
    have hqc1 : isOne (qc (Nat.pair i n)) = 1 := (isOne_eq_one_iff _).mpr ((hqcs _).mp hi)
    rw [hqc1, selectFn_one, unpair_pair_snd]
  · rintro ⟨w, rfl⟩
    exact hrw_mem w

variable {β : Type*}


theorem tFun_zero {W : NeighborhoodSystem β} (Q : ComputablePresentation W) (r : ℕ → ℕ) :
    tFun Q r 0 = r 0 := rfl

private theorem tFun_succ {W : NeighborhoodSystem β} (Q : ComputablePresentation W) (r : ℕ → ℕ)
    (i : ℕ) : tFun Q r (i + 1) = Q.inter (tFun Q r i) (r (i + 1)) := rfl

/-- The running-intersection enumeration is primitive recursive whenever `r` is (genuine primitive
recursion with a counter-dependent step, via `Nat.Primrec.prec`). -/
private theorem primrec_tFun {W : NeighborhoodSystem β} (Q : ComputablePresentation W) {r : ℕ → ℕ}
    (hr : Nat.Primrec r) : Nat.Primrec (tFun Q r) := by
  have hg : Nat.Primrec (fun w => Q.inter w.unpair.2.unpair.2 (r (w.unpair.2.unpair.1 + 1))) := by
    have hIH : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
      Nat.Primrec.right.comp Nat.Primrec.right
    have hy1 : Nat.Primrec (fun w : ℕ => r (w.unpair.2.unpair.1 + 1)) :=
      hr.comp (Nat.Primrec.succ.comp (Nat.Primrec.left.comp Nat.Primrec.right))
    exact (Q.inter_primrec.comp (hIH.pair hy1)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  refine ((Nat.Primrec.prec (Nat.Primrec.const (r 0)) hg).comp
    ((Nat.Primrec.const 0).pair primrec_id)).of_eq (fun n => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rfl

/-- **Exercise 7.14, Half 2 (Scott 1981, PRG-19).** Every computable element `y ∈ |ℰ|` can be
written `y = ⋃ {↑Y_{t(i)} ∣ i ∈ ℕ}` with `t : ℕ → ℕ` primitive recursive and the approximations
*decreasing*, `Y_{t(i+1)} ⊆ Y_{t(i)}`.

The index set `{m ∣ Yₘ ∈ y}` is r.e. (`ComputableElement`) and non-empty (it contains the master
`Δ`, by `y.master_mem`), so Half 1's `repred_exists_primrec_range` lists it as the range of a
primitive recursive `r₀`. Running intersections (`tFun Q r₀`) turn this into a decreasing chain whose
members are still in `y` (a filter is closed under `∩`) and still cofinal in `y` (each
`Y_{t(i)} ⊆ Y_{r₀(i)}`), so the principal-filter union is unchanged. -/
theorem computableElement_eq_decreasing_iUnion_principal {W : NeighborhoodSystem β}
    (Q : ComputablePresentation W) {y : W.Element} (hy : ComputableElement Q y) :
    ∃ t : ℕ → ℕ, Nat.Primrec t ∧
      (∀ i, Q.X (t (i + 1)) ⊆ Q.X (t i)) ∧
      (∀ Z, y.mem Z ↔ ∃ i, (W.principal (Q.mem_X (t i))).mem Z) := by
  have hy' : REPred (fun m => y.mem (Q.X m)) := hy.out
  -- The index set is non-empty: it contains the master neighbourhood `Δ`.
  obtain ⟨m₀, hm₀⟩ := Q.surj W.master_mem
  have hwit : y.mem (Q.X m₀) := by rw [hm₀]; exact y.master_mem
  obtain ⟨r₀, hr₀, hr0_spec⟩ := repred_exists_primrec_range hy' hwit
  -- Each enumerated index gives a member of `y`.
  have hr0_mem : ∀ i, y.mem (Q.X (r₀ i)) := fun i => (hr0_spec (r₀ i)).mpr ⟨i, rfl⟩
  -- Consistency of a pair of members (witnessed by their meet, itself in `y`).
  have hcons : ∀ a c : ℕ, y.mem (Q.X a) → y.mem (Q.X c) →
      ∃ k, Q.X k ⊆ Q.X a ∩ Q.X c := by
    intro a c ha hc
    obtain ⟨k, hk⟩ := Q.surj (y.sub (y.inter_mem ha hc))
    exact ⟨k, hk.subset⟩
  -- Every `tFun` value is a member of `y`.
  have ht_mem : ∀ i, y.mem (Q.X (tFun Q r₀ i)) := by
    intro i
    induction i with
    | zero => rw [tFun_zero]; exact hr0_mem 0
    | succ k ih =>
      have heq : Q.X (tFun Q r₀ (k + 1)) = Q.X (tFun Q r₀ k) ∩ Q.X (r₀ (k + 1)) :=
        Q.inter_spec (hcons (tFun Q r₀ k) (r₀ (k + 1)) ih (hr0_mem (k + 1)))
      rw [heq]; exact y.inter_mem ih (hr0_mem (k + 1))
  -- The defining intersection equation for `tFun`.
  have ht_eq : ∀ i, Q.X (tFun Q r₀ (i + 1)) = Q.X (tFun Q r₀ i) ∩ Q.X (r₀ (i + 1)) := fun i =>
    Q.inter_spec (hcons (tFun Q r₀ i) (r₀ (i + 1)) (ht_mem i) (hr0_mem (i + 1)))
  -- Decreasing: the next approximation is contained in the current one.
  have ht_dec : ∀ i, Q.X (tFun Q r₀ (i + 1)) ⊆ Q.X (tFun Q r₀ i) := by
    intro i; rw [ht_eq i]; exact Set.inter_subset_left
  -- Each approximation is contained in the corresponding enumerated member.
  have ht_sub_r : ∀ i, Q.X (tFun Q r₀ i) ⊆ Q.X (r₀ i) := by
    intro i
    cases i with
    | zero => rw [tFun_zero]
    | succ k => rw [ht_eq k]; exact Set.inter_subset_right
  refine ⟨tFun Q r₀, primrec_tFun Q hr₀, ht_dec, fun Z => ?_⟩
  constructor
  · intro hZ
    obtain ⟨m, hm⟩ := Q.surj (y.sub hZ)
    have hym : y.mem (Q.X m) := by rw [hm]; exact hZ
    obtain ⟨i, hi⟩ := (hr0_spec m).mp hym
    have hZeq : Q.X (r₀ i) = Z := by rw [hi]; exact hm
    exact ⟨i, y.sub hZ, by rw [← hZeq]; exact ht_sub_r i⟩
  · rintro ⟨i, hWZ, hsub⟩
    exact y.up_mem (ht_mem i) hWZ hsub
end DomainTheory.NeighbourhoodSystems.Exercise714
