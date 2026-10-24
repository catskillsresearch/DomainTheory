module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_9

@[expose] public section

section
/- concordance: source L4631 EXERCISE 7.14 primitive recursive witnesses -/
-- Exercise714/tFun.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise714

open NeighborhoodSystem Domain.Recursive DomainTheory.NeighbourhoodSystems

variable {β : Type*}

/-- The **running-intersection enumeration** of a computable element: `tFun Q r 0 = r 0` and
`tFun Q r (i+1) = Q.inter (tFun Q r i) (r (i+1))`. As `i` grows it lists the meet of the first `i+1`
members `Y_{r 0}, …, Y_{r i}` of the element, giving a *decreasing* chain of neighbourhoods. -/
def tFun {W : NeighborhoodSystem β} (Q : ComputablePresentation W) (r : ℕ → ℕ) (n : ℕ) :
    ℕ :=
  Nat.rec (motive := fun _ => ℕ) (r 0) (fun y IH => Q.inter IH (r (y + 1))) n

end DomainTheory.NeighbourhoodSystems.Exercise714
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise714
open NeighborhoodSystem Domain.Recursive DomainTheory.NeighbourhoodSystems

section
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
end

section
set_option linter.unusedVariables false

theorem example_714.{u_1} : ∀ {β : Type u_1} {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
  {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W},
  @DomainTheory.NeighbourhoodSystems.ComputableElement β W Q y →
    ∃ (t : Nat → Nat),
      And (Nat.Primrec t)
        (And
          (∀ (i : Nat),
            @LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q
                (t
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q (t i)))
          (∀ (Z : Set β),
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β W y Z)
              (∃ (i : Nat),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β W
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal β W
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q (t i))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.mem_X β W Q (t i)))
                  Z))) :=
  @DomainTheory.NeighbourhoodSystems.Exercise714.computableElement_eq_decreasing_iUnion_principal
end

section
/-- **The range of a primitive recursive function is recursively enumerable.** The relation
`r i = n` is recursively decidable (`RecDecidable.natEq`), and `∃ i, r i = n` is its projection, so
it is r.e. by definition of `REPred`. -/
theorem repred_range_primrec {r : ℕ → ℕ} (hr : Nat.Primrec r) :
    REPred (fun n => ∃ i, r i = n) := by
  refine ⟨fun t => r t.unpair.1 = t.unpair.2,
    RecDecidable.natEq (hr.comp Nat.Primrec.left) Nat.Primrec.right, fun n => ?_⟩
  refine exists_congr (fun i => ?_)
  simp only [unpair_pair_fst, unpair_pair_snd]
end

section
/-- **A non-empty recursively enumerable relation is enumerated by a pair of primitive recursive
functions** (Scott's `f = {(X_{s(i)}, Y_{r(i)}) ∣ i ∈ ℕ}`). Apply `repred_exists_primrec_range` to
the `Nat.pair`-coded relation and split the resulting range function into its two coordinates. -/
theorem repred₂_exists_primrec_enum {p : ℕ → ℕ → Prop} (hp : REPred₂ p) {a b : ℕ}
    (hab : p a b) :
    ∃ s r : ℕ → ℕ, Nat.Primrec s ∧ Nat.Primrec r ∧
      ∀ n m, p n m ↔ ∃ i, s i = n ∧ r i = m := by
  have hp' : REPred (fun t => p t.unpair.1 t.unpair.2) := hp
  have hwit : (fun t => p t.unpair.1 t.unpair.2) (Nat.pair a b) := by
    simp only [unpair_pair_fst, unpair_pair_snd]; exact hab
  obtain ⟨pf, hpf, hspec⟩ := repred_exists_primrec_range hp' hwit
  refine ⟨fun i => (pf i).unpair.1, fun i => (pf i).unpair.2,
    Nat.Primrec.left.comp hpf, Nat.Primrec.right.comp hpf, fun n m => ?_⟩
  have h := hspec (Nat.pair n m)
  simp only [unpair_pair_fst, unpair_pair_snd] at h
  rw [h]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, ?_⟩
    · show (pf i).unpair.1 = n; rw [hi, unpair_pair_fst]
    · show (pf i).unpair.2 = m; rw [hi, unpair_pair_snd]
  · rintro ⟨i, hs, hr⟩
    refine ⟨i, ?_⟩
    change (pf i).unpair.1 = n at hs
    change (pf i).unpair.2 = m at hr
    rw [← hs, ← hr]; exact (pair_unpair _).symm
end

end DomainTheory.NeighbourhoodSystems.Exercise714
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

section
namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Each product term `↓X ∩ ↓Y` is a `ℙ𝒟`-neighbourhood.** By `upSet_inter` it is `↓(X ∩ Y)`; if
`{X, Y}` is consistent (`X ∩ Y ∈ 𝒟`) this is the down-set of a neighbourhood (`PDmem_upSet`),
otherwise `↓(X ∩ Y) = ∅` (no `Z ∈ 𝒟` lies below `X ∩ Y`), the empty union (`PDmem_empty`). The
`by_cases` on `V.mem (X ∩ Y)` is the lone `Classical` step (deciding membership in an arbitrary
system). -/
theorem PDmem_upSet_inter {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.PDmem (V.upSet X ∩ V.upSet Y) := by
  rw [V.upSet_inter]
  by_cases h : V.mem (X ∩ Y)
  · exact V.PDmem_upSet h
  · have hempty : V.upSet (X ∩ Y) = ∅ := by
      ext Z
      simp only [mem_upSet, Set.mem_empty_iff_false, iff_false, not_and]
      intro hZmem hZsub
      exact h (V.inter_mem hX hY hZmem hZsub)
    rw [hempty]; exact V.PDmem_empty

/-- Cons law for the finite union of down-sets: `⋃_{X ∈ Y::L} ↓X = ↓Y ∪ ⋃_{X ∈ L} ↓X`. -/
theorem upSetUnion_cons (Y : Set α) (L : List (Set α)) :
    (⋃ X ∈ (Y :: L), V.upSet X) = V.upSet Y ∪ ⋃ X ∈ L, V.upSet X := by
  ext z
  rw [Set.mem_union, V.mem_PDunion, V.mem_PDunion]
  constructor
  · rintro ⟨X, hX, hz⟩
    rcases List.mem_cons.mp hX with rfl | hX'
    · exact Or.inl hz
    · exact Or.inr ⟨X, hX', hz⟩
  · rintro (hz | ⟨X, hX, hz⟩)
    · exact ⟨Y, List.mem_cons.mpr (Or.inl rfl), hz⟩
    · exact ⟨X, List.mem_cons.mpr (Or.inr hX), hz⟩

/-- The finite union `⋃_{X ∈ []} ↓X` is empty. -/
theorem upSetUnion_nil : (⋃ X ∈ ([] : List (Set α)), V.upSet X) = ∅ := by
  ext z
  rw [V.mem_PDunion]
  simp only [List.not_mem_nil, false_and, exists_false, Set.mem_empty_iff_false]

/-- `↓X ∩ (⋃_{Y ∈ L} ↓Y) ∈ ℙ𝒟`: distribute `∩` over the finite union and use `PDmem_upSet_inter`
term by term. -/
theorem PDmem_upSet_inter_biUnion {X : Set α} (hX : V.mem X) :
    ∀ (L : List (Set α)), (∀ Y ∈ L, V.mem Y) → V.PDmem (V.upSet X ∩ ⋃ Y ∈ L, V.upSet Y) := by
  intro L
  induction L with
  | nil =>
    intro _
    rw [V.upSetUnion_nil, Set.inter_empty]
    exact V.PDmem_empty
  | cons Y L ih =>
    intro hL
    rw [V.upSetUnion_cons, Set.inter_union_distrib_left]
    exact V.PDmem_union (V.PDmem_upSet_inter hX (hL Y (List.mem_cons.mpr (Or.inl rfl))))
      (ih (fun Z hZ => hL Z (List.mem_cons.mpr (Or.inr hZ))))

/-- `(⋃_{X ∈ L₁} ↓X) ∩ W₂ ∈ ℙ𝒟` for any `ℙ𝒟`-neighbourhood `W₂` (induction on `L₁`). -/
theorem PDmem_biUnion_inter :
    ∀ (L₁ : List (Set α)), (∀ X ∈ L₁, V.mem X) → ∀ {W₂ : Set (Set α)}, V.PDmem W₂ →
      V.PDmem ((⋃ X ∈ L₁, V.upSet X) ∩ W₂) := by
  intro L₁
  induction L₁ with
  | nil =>
    intro _ W₂ _
    rw [V.upSetUnion_nil, Set.empty_inter]
    exact V.PDmem_empty
  | cons X L ih =>
    intro hL W₂ hW₂
    rw [V.upSetUnion_cons, Set.union_inter_distrib_right]
    refine V.PDmem_union ?_ (ih (fun Z hZ => hL Z (List.mem_cons.mpr (Or.inr hZ))) hW₂)
    obtain ⟨L₂, hL₂, rfl⟩ := hW₂
    exact V.PDmem_upSet_inter_biUnion (hL X (List.mem_cons.mpr (Or.inl rfl))) L₂ hL₂

/-- **`ℙ𝒟` is closed under binary intersection.** (The content of Part A's condition (ii).) -/
theorem PDmem_inter {W₁ W₂ : Set (Set α)} (h₁ : V.PDmem W₁) (h₂ : V.PDmem W₂) :
    V.PDmem (W₁ ∩ W₂) := by
  obtain ⟨L₁, hL₁, rfl⟩ := h₁
  exact V.PDmem_biUnion_inter L₁ hL₁ h₂

end NeighborhoodSystem
end
end DomainTheory.NeighbourhoodSystems
end
