module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example_6_1
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_15

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap ExampleB
namespace Example62

/- concordance: source L3510 EXAMPLE 6.2 sequence domain equations -/
/-- **Example 6.2 — the shape of a `B`-neighbourhood.** Every neighbourhood of `B` is either the
master `Σ* = cone []`, a `0`-copy `0X` with `X ∈ B`, or a `1`-copy `1X` with `X ∈ B`. -/
theorem memB_cases {W : Set Str} (hW : B.mem W) :
    W = Set.univ ∨ (∃ X, B.mem X ∧ W = embBit false X) ∨ (∃ Y, B.mem Y ∧ W = embBit true Y) := by
  obtain ⟨σ, rfl⟩ := hW
  cases σ with
  | nil => exact Or.inl cone_nil
  | cons b σ' =>
    cases b with
    | false => exact Or.inr (Or.inl ⟨cone σ', memB_cone σ', (embBit_cone false σ').symm⟩)
    | true => exact Or.inr (Or.inr ⟨cone σ', memB_cone σ', (embBit_cone true σ').symm⟩)

/-- Prepending a bit lands back in `B`. -/
theorem memB_embBit (b : Bool) {X : Set Str} (hX : B.mem X) : B.mem (embBit b X) := by
  rw [embBit_eq_prepend]; exact memB_prepend [b] hX

/-- If `bW ∈ B` then `W ∈ B`: a `b`-prefixed neighbourhood that lands in `B` must be `b·(cone w')`,
so `W = cone w'`. -/
theorem memB_embBit_inv {b : Bool} {W : Set Str} (h : B.mem (embBit b W)) : B.mem W := by
  obtain ⟨σ, hσ⟩ := h
  have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
  obtain ⟨w', rfl, -⟩ := hmem
  rw [← embBit_cone] at hσ
  rw [embBit_injective hσ]
  exact memB_cone w'

theorem nil_not_mem_embBit {b : Bool} {X : Set Str} : ([] : Str) ∉ embBit b X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

theorem embBit_ne_univ (b : Bool) (X : Set Str) : embBit b X ≠ Set.univ := by
  intro h; exact nil_not_mem_embBit (X := X) (b := b) (by rw [h]; trivial)

theorem sum_mem_inj₀_inv {X : Set Str} (h : BB.mem (inj₀ X)) : B.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := B_nonempty Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

theorem sum_mem_inj₁_inv {Y : Set Str} (h : BB.mem (inj₁ Y)) : B.mem Y := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := B_nonempty X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

theorem sum_mem_nonempty {W : Set (Option (Str ⊕ Str))} (h : BB.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (B_nonempty X hX)
  · exact inj₁_nonempty (B_nonempty Y hY)

/-- **Example 6.2 — forward half of `B ≅ B + B`.** An element `x` of `B` is sent to the sum element
recording, for each branch, whether `x` reaches the `0`-copy `0X` (left summand) or the `1`-copy `1Y`
(right summand). -/
def toBB (x : B.Element) : BB.Element where
  mem W := W = sumMaster B B
    ∨ (∃ X, B.mem X ∧ W = inj₀ X ∧ x.mem (embBit false X))
    ∨ (∃ Y, B.mem Y ∧ W = inj₁ Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := x.inter_mem hzX hzX'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzX hzX'; rwa [embBit_inter] at hz
    · exfalso
      have hz := x.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumMaster_inter_inj₁ hY], hzY⟩)
    · exfalso
      have hz := x.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [inj₁_inter], ?_⟩)
      · have hz := x.inter_mem hzY hzY'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzY hzY'; rwa [embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact x.up_mem hzX (memB_embBit false hX') (embBit_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact x.up_mem hzY (memB_embBit true hY') (embBit_subset.mpr (inj₁_subset_inj₁.mp hsub))

@[simp] theorem toBB_mem_inj₀ {x : B.Element} {X : Set Str} (hX : B.mem X) :
    (toBB x).mem (inj₀ X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := B_nonempty X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toBB_mem_inj₁ {x : B.Element} {Y : Set Str} (hY : B.mem Y) :
    (toBB x).mem (inj₁ Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := B_nonempty X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rwa [inj₁_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

/-- **Example 6.2 — inverse half of `B ≅ B + B`.** -/
def fromBB (s : BB.Element) : B.Element where
  mem W := W = Set.univ
    ∨ (∃ X, B.mem X ∧ W = embBit false X ∧ s.mem (inj₀ X))
    ∨ (∃ Y, B.mem Y ∧ W = embBit true Y ∧ s.mem (inj₁ Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact ⟨[], cone_nil.symm⟩
    · exact memB_embBit false hX
    · exact memB_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [inj₁_inter] at hs
        exact sum_mem_inj₁_inv (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [inj₁_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact s.up_mem hsY (Or.inr (Or.inr ⟨Y', hY', rfl⟩))
          (inj₁_subset_inj₁.mpr (embBit_subset.mp hsub))

@[simp] theorem fromBB_mem_embF {s : BB.Element} {X : Set Str} (hX : B.mem X) :
    (fromBB s).mem (embBit false X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X hX))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromBB_mem_embT {s : BB.Element} {Y : Set Str} (hY : B.mem Y) :
    (fromBB s).mem (embBit true Y) ↔ s.mem (inj₁ Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X' hX'))
    · rwa [embBit_injective heq]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

theorem fromBB_toBB (x : B.Element) : fromBB (toBB x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact (toBB_mem_inj₀ hX).mp hs
    · exact (toBB_mem_inj₁ hY).mp hs
  · intro hW
    rcases memB_cases (x.sub hW) with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (toBB_mem_inj₀ hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (toBB_mem_inj₁ hY).mpr hW⟩)

theorem toBB_fromBB (s : BB.Element) : toBB (fromBB s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromBB_mem_embF hX).mp hs
    · exact (fromBB_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromBB_mem_embF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromBB_mem_embT hY).mpr hW⟩)

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|B| ≃o |B + B|`.** -/
def bbEquiv : B.Element ≃o BB.Element where
  toFun := toBB
  invFun := fromBB
  left_inv := fromBB_toBB
  right_inv := toBB_fromBB
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases memB_cases (x.sub hX) with rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact (toBB_mem_inj₀ hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      · exact (toBB_mem_inj₁ hA).mp (h _ (Or.inr (Or.inr ⟨A, hA, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `B ≅ B + B`.** Scott's binary-sequence
domain `B` is, as a domain, isomorphic to `B + B`: a sequence is bottom, or begins with `0`, or begins
with `1`, the two non-bottom cases giving the two summands. -/
theorem B_domain_equation : B ≅ᴰ sum B B B_nonempty B_nonempty :=
  ⟨bbEquiv⟩

theorem embBit_nonempty {b : Bool} {X : Set Str} (hX : X.Nonempty) : (embBit b X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨b :: w', w', rfl, hw'⟩

end Example62
end

namespace Example62A
open NeighborhoodSystem ApproximableMap ExampleB

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- The slot prefix `i 1ʲ 0`: the leading tag bit `i` (Scott's `+/−`), then `j` ones, then a zero.
Reaching component `j` of the tag-`i` tuple means matching this prefix. -/
def slotPre (i : Bool) (j : ℕ) : Str := i :: (List.replicate j true ++ [false])

/-- **Scott's tag-`i` tuple neighbourhood** `i ⋃_{j<n} 1ʲ0 X_j`: the union of the `n` slots, slot `j`
holding `X j` behind the prefix `i 1ʲ 0`. (For `i = false`/`true` these are Scott's left/right
copies, the `−`/`+` summands.) -/
def embTuple (i : Bool) (X : Fin n → Set Str) : Set Str :=
  {w | ∃ j : Fin n, ∃ w', w = slotPre i (j : ℕ) ++ w' ∧ w' ∈ X j}

/-- **Scott's domain `A`** as the *least* family of subsets of `Σ* = {0,1}*` containing (i) the master
`Σ*` and (ii) every tag-`i` tuple `i ⋃_{j<n} 1ʲ0 X_j` built from components `X j` already in `A`:

`A = {Σ*} ∪ ⋃_{i∈{0,1}} { i ⋃_{j<n} 1ʲ0 X_j ∣ X_j ∈ A }`. -/
inductive MemA (n : ℕ) : Set Str → Prop
  | univ : MemA n Set.univ
  | tuple (i : Bool) {X : Fin n → Set Str} : (∀ j, MemA n (X j)) → MemA n (embTuple i X)

end

section
variable {β : Type*} {n : ℕ}

/-- The *proper product* neighbourhood `⋃_{j<n} {j} × X_j`: token `(j, b)` lies in it iff `b ∈ X_j`.
This is the `n`-ary analogue of `prodNbhd` (Definition 3.1). -/
def prodN (X : Fin n → Set β) : Set (Fin n × β) := {p | p.2 ∈ X p.1}

@[simp] theorem mem_prodN {X : Fin n → Set β} {p : Fin n × β} : p ∈ prodN X ↔ p.2 ∈ X p.1 := Iff.rfl

theorem prodN_injective {X X' : Fin n → Set β} (h : prodN X = prodN X') : ∀ j, X j = X' j := by
  intro j; ext b
  have := Set.ext_iff.mp h (j, b)
  simpa only [mem_prodN] using this

theorem prodN_inter {X X' : Fin n → Set β} :
    prodN X ∩ prodN X' = prodN (fun j => X j ∩ X' j) := by
  ext p; simp only [Set.mem_inter_iff, mem_prodN]

theorem prodN_subset {X X' : Fin n → Set β} : prodN X ⊆ prodN X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j b hb; exact h (show (j, b) ∈ prodN X from hb)
  · intro h p hp; exact h p.1 hp

/-- **The positive `n`-fold product `Vⁿ`** of a neighbourhood system `V`, over `Fin n × β`.
The assumption `0 < n` is necessary because Scott's token set `Fin n × Δ` must be non-empty.
Its neighbourhoods are exactly the proper products `prodN X` with each component `X j ∈ V`;
closure under intersection is componentwise. -/
def npow (V : NeighborhoodSystem β) (n : ℕ) (hn : 0 < n) : NeighborhoodSystem (Fin n × β) where
  mem W := ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X
  master := prodN (fun _ => V.master)
  master_nonempty := by
    obtain ⟨b, hb⟩ := V.master_nonempty
    exact ⟨(⟨0, hn⟩, b), hb⟩
  master_mem := ⟨_, fun _ => V.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, hX, rfl⟩ ⟨X', hX', rfl⟩ ⟨Zw, hZw, rfl⟩ hsub
    refine ⟨fun j => X j ∩ X' j, ?_, prodN_inter⟩
    intro j
    rw [prodN_inter] at hsub
    exact V.inter_mem (hX j) (hX' j) (hZw j) (prodN_subset.mp hsub j)
  sub_master := by
    rintro W ⟨X, hX, rfl⟩
    exact prodN_subset.mpr (fun j => V.sub_master (hX j))

@[simp] theorem npow_mem {V : NeighborhoodSystem β} {W : Set (Fin n × β)} {hn : 0 < n} :
    (npow V n hn).mem W ↔ ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X := Iff.rfl

end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem mem_embTuple {i : Bool} {X : Fin n → Set Str} {w : Str} :
    w ∈ embTuple i X ↔ ∃ j : Fin n, ∃ w', w = slotPre i (j : ℕ) ++ w' ∧ w' ∈ X j := Iff.rfl

theorem embTuple_nonempty {i : Bool} {X : Fin n → Set Str} (j : Fin n) (h : (X j).Nonempty) :
    (embTuple i X).Nonempty := by
  obtain ⟨a, ha⟩ := h
  exact ⟨slotPre i (j : ℕ) ++ a, j, a, rfl, ha⟩

/-- Under `0 < n` every neighbourhood of `A` is non-empty (Scott's `∅ ∉ A`). -/
theorem memA_nonempty (hn : 0 < n) : ∀ {W}, MemA n W → W.Nonempty := by
  intro W hW
  induction hW with
  | univ => exact ⟨[], Set.mem_univ []⟩
  | tuple i hX ih => exact embTuple_nonempty ⟨0, hn⟩ (ih ⟨0, hn⟩)

theorem nil_not_mem_embTuple {i : Bool} {X : Fin n → Set Str} : ([] : Str) ∉ embTuple i X := by
  rintro ⟨j, a, heq, -⟩
  rw [slotPre, List.cons_append] at heq
  exact List.cons_ne_nil _ _ heq.symm

theorem embTuple_ne_univ {i : Bool} (X : Fin n → Set Str) : embTuple i X ≠ Set.univ := by
  intro h
  have : ([] : Str) ∈ embTuple i X := by rw [h]; exact Set.mem_univ []
  exact nil_not_mem_embTuple this

end

section
variable {β : Type*} {n : ℕ}

/-- Under Scott's standing assumption `∅ ∉ V`, no neighbourhood of `Vⁿ` is empty (provided `0 < n`,
so there is a coordinate to witness). -/
theorem npow_nonempty {V : NeighborhoodSystem β} (hn : 0 < n)
    (hV : ∀ X, V.mem X → X.Nonempty) : ∀ W, (npow V n hn).mem W → W.Nonempty := by
  rintro W ⟨X, hX, rfl⟩
  obtain ⟨b, hb⟩ := hV (X ⟨0, hn⟩) (hX ⟨0, hn⟩)
  exact ⟨(⟨0, hn⟩, b), hb⟩

/-- Parsing the `1ʲ0` body: the position of the first `false` pins down `j` and the remainder. -/
theorem slot_list_inj : ∀ (j j' : ℕ) (u v : Str),
    List.replicate j true ++ false :: u = List.replicate j' true ++ false :: v → j = j' ∧ u = v
  | 0, 0, u, v, h => by simpa using h
  | 0, j' + 1, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, 0, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, j' + 1, u, v, h => by
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append,
        List.cons.injEq] at h
      obtain ⟨hj, hu⟩ := slot_list_inj j j' u v h.2
      exact ⟨by rw [hj], hu⟩

/-- **Uniqueness of slot decomposition.** A token `i 1ʲ 0 u` determines the tag `i`, the index `j`,
and the remainder `u`. This is what makes the slots pairwise disjoint. -/
theorem slotPre_inj {i i' : Bool} {j j' : ℕ} {u v : Str}
    (h : slotPre i j ++ u = slotPre i' j' ++ v) : i = i' ∧ j = j' ∧ u = v := by
  rw [slotPre, slotPre, List.cons_append, List.cons_append, List.cons.injEq] at h
  obtain ⟨hi, hrest⟩ := h
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append] at hrest
  obtain ⟨hj, huv⟩ := slot_list_inj j j' u v hrest
  exact ⟨hi, hj, huv⟩

end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_inter {i : Bool} (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i X' = embTuple i (fun j => X j ∩ X' j) := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple]
  constructor
  · rintro ⟨⟨j, a, rfl, ha⟩, ⟨j', a', heq, ha'⟩⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ⟨j, a, rfl, ha, ha'⟩
  · rintro ⟨j, a, rfl, ha, ha'⟩
    exact ⟨⟨j, a, rfl, ha⟩, ⟨j, a, rfl, ha'⟩⟩

theorem embTuple_inter_ne {i i' : Bool} (h : i ≠ i') (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i' X' = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨j, a, rfl, ha⟩ ⟨j', a', heq, ha'⟩
  exact h (slotPre_inj heq).1

theorem embTuple_ne {i i' : Bool} (h : i ≠ i') {X Y : Fin n → Set Str} (j : Fin n)
    (hX : (X j).Nonempty) : embTuple i X ≠ embTuple i' Y := by
  intro heq
  obtain ⟨a, ha⟩ := hX
  have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' Y := heq ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
  obtain ⟨j', a', he, -⟩ := hmem
  exact h (slotPre_inj he).1

theorem embTuple_subset {i : Bool} {X X' : Fin n → Set Str} :
    embTuple i X ⊆ embTuple i X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j a ha
    obtain ⟨j', a', heq, ha'⟩ := h ⟨j, a, rfl, ha⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ha'
  · rintro h w ⟨j, a, rfl, ha⟩
    exact ⟨j, a, rfl, h j ha⟩

theorem embTuple_injective {i : Bool} {X X' : Fin n → Set Str}
    (h : embTuple i X = embTuple i X') : ∀ j, X j = X' j := by
  intro j
  exact Set.Subset.antisymm (embTuple_subset.mp h.subset j) (embTuple_subset.mp h.symm.subset j)

/-- Inversion: the components of a tuple-shaped neighbourhood of `A` are themselves in `A`. -/
theorem memA_tuple_inv (hn : 0 < n) {i : Bool} {X : Fin n → Set Str}
    (h : MemA n (embTuple i X)) : ∀ j, MemA n (X j) := by
  generalize hW : embTuple i X = W at h
  cases h with
  | univ =>
    exfalso
    have : ([] : Str) ∈ embTuple i X := by rw [hW]; exact Set.mem_univ []
    exact nil_not_mem_embTuple this
  | @tuple i' X' hX' =>
    have hne : (embTuple i' X').Nonempty :=
      embTuple_nonempty ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩))
    rw [← hW] at hne
    obtain ⟨w, j, a, rfl, ha⟩ := hne
    have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' X' := hW ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
    obtain ⟨j', a', he, -⟩ := hmem
    have hii : i = i' := (slotPre_inj he).1
    subst hii
    intro k; rw [embTuple_injective hW k]; exact hX' k

/-- A non-empty witness contained in a tag-`i'` tuple must carry the tag `i'`. -/
theorem tag_eq_of_subset (hn : 0 < n) {i i' : Bool} {Z V : Fin n → Set Str}
    (hZ : ∀ j, MemA n (Z j)) (hsub : embTuple i Z ⊆ embTuple i' V) : i = i' := by
  obtain ⟨a, ha⟩ := memA_nonempty hn (hZ ⟨0, hn⟩)
  obtain ⟨j', v, he, -⟩ := hsub ⟨⟨0, hn⟩, a, rfl, ha⟩
  exact (slotPre_inj he).1

/-- **`A` is closed under consistent intersection.** Scott's verification, by induction on the way `X`
entered `A`: the cross case `embTuple false · ∩ embTuple true ·` collapses to `∅` (killed by the
non-empty witness), the same-tag case combines componentwise (recursing on the consistency witness's
slots). -/
theorem memA_inter (hn : 0 < n) :
    ∀ {X}, MemA n X → ∀ {Y}, MemA n Y → ∀ {Z}, MemA n Z → Z ⊆ X ∩ Y → MemA n (X ∩ Y) := by
  intro X hX
  induction hX with
  | univ =>
    intro Y hY Z _ _
    rw [Set.univ_inter]; exact hY
  | @tuple i X hX ih =>
    intro Y hY Z hZ hsub
    cases hY with
    | univ =>
      rw [Set.inter_univ]; exact MemA.tuple i hX
    | @tuple i' X' hX' =>
      by_cases hii : i = i'
      · rw [hii, embTuple_inter] at hsub ⊢
        cases hZ with
        | univ => exact absurd (hsub (Set.mem_univ [])) nil_not_mem_embTuple
        | @tuple i'' ZW hZW =>
          have htag : i'' = i' := tag_eq_of_subset hn hZW hsub
          rw [htag] at hsub
          have hZsub := embTuple_subset.mp hsub
          exact MemA.tuple i' (fun j => ih j (hX' j) (hZW j) (hZsub j))
      · rw [embTuple_inter_ne hii] at hsub ⊢
        exfalso
        obtain ⟨z, hz⟩ := memA_nonempty hn hZ
        exact Set.notMem_empty z (hsub hz)

/-- **Scott's domain `A`** packaged as a neighbourhood system over `{0,1}*` (needs `0 < n`). -/
def Asys (n : ℕ) (hn : 0 < n) : NeighborhoodSystem Str where
  mem := MemA n
  master := Set.univ
  master_nonempty := ⟨[], Set.mem_univ _⟩
  master_mem := MemA.univ
  inter_mem := fun hX hY hZ hsub => memA_inter hn hX hY hZ hsub
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem Asys_mem {hn : 0 < n} {W : Set Str} : (Asys n hn).mem W ↔ MemA n W := Iff.rfl

@[simp] theorem Asys_master {hn : 0 < n} : (Asys n hn).master = Set.univ := rfl

/-- The `n`-fold product `Aⁿ = npow A n`. -/
abbrev Apow (hn : 0 < n) : NeighborhoodSystem (Fin n × Str) := npow (Asys n hn) n hn

theorem apowNe (hn : 0 < n) : ∀ W, (Apow hn).mem W → W.Nonempty :=
  npow_nonempty hn (fun _ h => memA_nonempty hn h)

/-- The right-hand side of Scott's equation: the separated sum `Aⁿ + Aⁿ`. -/
abbrev AAsys (hn : 0 < n) : NeighborhoodSystem (Option ((Fin n × Str) ⊕ (Fin n × Str))) :=
  sum (Apow hn) (Apow hn) (apowNe hn) (apowNe hn)

theorem aa_mem_inj₀_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₀ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := apowNe hn _ hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

theorem aa_mem_inj₁_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₁ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := apowNe hn _ hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

theorem aa_mem_nonempty (hn : 0 < n) {W : Set (Option ((Fin n × Str) ⊕ (Fin n × Str)))}
    (h : (AAsys hn).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (apowNe hn _ hX)
  · exact inj₁_nonempty (apowNe hn _ hY)

theorem apow_mem_prodN (hn : 0 < n) {X : Fin n → Set Str} (hX : ∀ j, MemA n (X j)) :
    (Apow hn).mem (prodN X) := ⟨X, hX, rfl⟩

theorem aa_mem_inj₀ (hn : 0 < n) {X : Fin n → Set Str} (hX : ∀ j, MemA n (X j)) :
    (AAsys hn).mem (inj₀ (prodN X)) := Or.inr (Or.inl ⟨prodN X, apow_mem_prodN hn hX, rfl⟩)

theorem aa_mem_inj₁ (hn : 0 < n) {Y : Fin n → Set Str} (hY : ∀ j, MemA n (Y j)) :
    (AAsys hn).mem (inj₁ (prodN Y)) := Or.inr (Or.inr ⟨prodN Y, apow_mem_prodN hn hY, rfl⟩)

theorem apow_mem_prodN_inv (hn : 0 < n) {X : Fin n → Set Str} (h : (Apow hn).mem (prodN X)) :
    ∀ j, MemA n (X j) := by
  obtain ⟨X', hX', heq⟩ := h
  intro j; rw [prodN_injective heq j]; exact hX' j

/-- **Forward half of `A ≅ Aⁿ + Aⁿ`.** An element `z` of `A` is sent to the sum element recording, for
each branch, whether `z` reaches the left copy `0X` (left summand `Aⁿ`) or the right copy `1Y` (right
summand `Aⁿ`). -/
def toAA (hn : 0 < n) (z : (Asys n hn).Element) : (AAsys hn).Element where
  mem W := W = sumMaster (Apow hn) (Apow hn)
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = inj₀ (prodN X) ∧ z.mem (embTuple false X))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = inj₁ (prodN Y) ∧ z.mem (embTuple true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact (AAsys hn).master_mem
    · exact aa_mem_inj₀ hn hX
    · exact aa_mem_inj₁ hn hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ (apow_mem_prodN hn hX')], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ (apow_mem_prodN hn hY')], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_comm, sumMaster_inter_inj₀ (apow_mem_prodN hn hX)], hzX⟩)
    · refine Or.inr (Or.inl ⟨fun j => X j ∩ X' j, ?_, by rw [inj₀_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embTuple_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzY'
      rw [embTuple_inter_ne (by decide : (false : Bool) ≠ true)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (apow_mem_prodN hn hY)], hzY⟩)
    · exfalso
      have hz := z.inter_mem hzY hzX'
      rw [embTuple_inter_ne (by decide : (true : Bool) ≠ false)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j, ?_, by rw [inj₁_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzY hzY'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzY hzY'; rwa [embTuple_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X', hX', rfl⟩ := hV'
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemA.tuple false hX')
          (embTuple_subset.mpr (prodN_subset.mp (inj₀_subset_inj₀.mp hsub)))
      · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
        exact absurd (hsub (il_mem_inj₀.mpr hb)) il_mem_inj₁
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := apowNe hn (prodN Y) (apow_mem_prodN hn hY)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨Y', hY', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact z.up_mem hzY (MemA.tuple true hY')
          (embTuple_subset.mpr (prodN_subset.mp (inj₁_subset_inj₁.mp hsub)))

@[simp] theorem toAA_mem_inj₀ (hn : 0 < n) {z : (Asys n hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (toAA hn z).mem (inj₀ (prodN X)) ↔ z.mem (embTuple false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rw [funext (prodN_injective (inj₀_injective heq))]; exact hz
    · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
      exact absurd (heq ▸ il_mem_inj₀.mpr hb) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toAA_mem_inj₁ (hn : 0 < n) {z : (Asys n hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (toAA hn z).mem (inj₁ (prodN Y)) ↔ z.mem (embTuple true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := apowNe hn (prodN X') (apow_mem_prodN hn hX')
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rw [funext (prodN_injective (inj₁_injective heq))]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

/-- **Inverse half of `A ≅ Aⁿ + Aⁿ`.** -/
def fromAA (hn : 0 < n) (s : (AAsys hn).Element) : (Asys n hn).Element where
  mem W := W = Set.univ
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = embTuple false X ∧ s.mem (inj₀ (prodN X)))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = embTuple true Y ∧ s.mem (inj₁ (prodN Y)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact MemA.univ
    · exact MemA.tuple false hX
    · exact MemA.tuple true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · have hs := s.inter_mem hsX hsX'
      rw [inj₀_inter, prodN_inter] at hs
      exact Or.inr (Or.inl ⟨fun j => X j ∩ X' j,
        apow_mem_prodN_inv hn (aa_mem_inj₀_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · have hs := s.inter_mem hsY hsY'
      rw [inj₁_inter, prodN_inter] at hs
      exact Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j,
        apow_mem_prodN_inv hn (aa_mem_inj₁_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : false = i'' := tag_eq_of_subset hn hX hsub
        subst htag
        refine Or.inr (Or.inl ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsX (aa_mem_inj₀ hn hV)
          (inj₀_subset_inj₀.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : true = i'' := tag_eq_of_subset hn hY hsub
        subst htag
        refine Or.inr (Or.inr ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsY (aa_mem_inj₁ hn hV)
          (inj₁_subset_inj₁.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))

@[simp] theorem fromAA_mem_embF (hn : 0 < n) {s : (AAsys hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (fromAA hn s).mem (embTuple false X) ↔ s.mem (inj₀ (prodN X)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ X)
    · rw [funext (embTuple_injective heq)]; exact hs
    · exact absurd heq
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX ⟨0, hn⟩)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromAA_mem_embT (hn : 0 < n) {s : (AAsys hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (fromAA hn s).mem (embTuple true Y) ↔ s.mem (inj₁ (prodN Y)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ Y)
    · exact absurd heq.symm
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩)))
    · rw [funext (embTuple_injective heq)]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

theorem fromAA_toAA (hn : 0 < n) (z : (Asys n hn).Element) : fromAA hn (toAA hn z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toAA_mem_inj₀ hn hX).mp hs
    · exact (toAA_mem_inj₁ hn hY).mp hs
  · intro hW
    cases z.sub hW with
    | univ => exact Or.inl rfl
    | @tuple i X hX =>
      cases i with
      | false => exact Or.inr (Or.inl ⟨X, hX, rfl, (toAA_mem_inj₀ hn hX).mpr hW⟩)
      | true => exact Or.inr (Or.inr ⟨X, hX, rfl, (toAA_mem_inj₁ hn hX).mpr hW⟩)

theorem toAA_fromAA (hn : 0 < n) (s : (AAsys hn).Element) : toAA hn (fromAA hn s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromAA_mem_embF hn hX).mp hs
    · exact (fromAA_mem_embT hn hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨X, hX, rfl⟩ := hV
      exact Or.inr (Or.inl ⟨X, hX, rfl, (fromAA_mem_embF hn hX).mpr hW⟩)
    · obtain ⟨Y, hY, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromAA_mem_embT hn hY).mpr hW⟩)

/-- **The isomorphism `|A| ≃o |Aⁿ + Aⁿ|`.** -/
def aaEquiv (hn : 0 < n) : (Asys n hn).Element ≃o (AAsys hn).Element where
  toFun := toAA hn
  invFun := fromAA hn
  left_inv := fromAA_toAA hn
  right_inv := toAA_fromAA hn
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      cases z.sub hW with
      | univ => exact z'.master_mem
      | @tuple i X hX =>
        cases i with
        | false => exact (toAA_mem_inj₀ hn hX).mp (h _ (Or.inr (Or.inl ⟨X, hX, rfl, hW⟩)))
        | true => exact (toAA_mem_inj₁ hn hX).mp (h _ (Or.inr (Or.inr ⟨X, hX, rfl, hW⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `A ≅ Aⁿ + Aⁿ`.** Scott's "simple, yet
interesting generalization of `B`": the domain `A` over `{0,1}*` (whose non-`⊥` elements are the two
copies — left `−` and right `+` — of an `n`-tuple of elements of `A`) is isomorphic to the separated
sum `Aⁿ + Aⁿ` of two copies of its own `n`-fold cartesian power. -/
theorem A_domain_equation (hn : 0 < n) : Asys n hn ≅ᴰ AAsys hn := ⟨aaEquiv hn⟩

end

end Example62A
open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

section
/-- Left tag `0a = some (inl a)`. -/
def t0 {α β γ : Type*} (a : α) : Option (α ⊕ β ⊕ γ) := some (Sum.inl a)
end

section
/-- The tagged left copy `0X`. -/
def j0 {α β γ : Type*} (X : Set α) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ a, w = t0 a ∧ a ∈ X}
end

section
variable {α β γ : Type*}

@[simp] theorem t0_mem_j0 {X : Set α} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∈ j0 X ↔ a ∈ X := by
  constructor
  · rintro ⟨a', heq, ha'⟩; simp only [t0, Option.some.injEq, Sum.inl.injEq] at heq; exact heq ▸ ha'
  · intro ha; exact ⟨a, rfl, ha⟩
end

section
/-- Middle tag `1b = some (inr (inl b))`. -/
def t1 {α β γ : Type*} (b : β) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inl b))
end

section
/-- The tagged middle copy `1Y`. -/
def j1 {α β γ : Type*} (Y : Set β) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ b, w = t1 b ∧ b ∈ Y}
end

section
variable {α β γ : Type*}

@[simp] theorem t1_mem_j1 {Y : Set β} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∈ j1 Y ↔ b ∈ Y := by
  constructor
  · rintro ⟨b', heq, hb'⟩
    simp only [t1, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at heq; exact heq ▸ hb'
  · intro hb; exact ⟨b, rfl, hb⟩
end

section
/-- Right tag `2c = some (inr (inr c))`. -/
def t2 {α β γ : Type*} (c : γ) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inr c))
end

section
/-- The tagged right copy `2Z`. -/
def j2 {α β γ : Type*} (Z : Set γ) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ c, w = t2 c ∧ c ∈ Z}
end

section
variable {α β γ : Type*}

@[simp] theorem t2_mem_j2 {Z : Set γ} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∈ j2 Z ↔ c ∈ Z := by
  constructor
  · rintro ⟨c', heq, hc'⟩
    simp only [t2, Option.some.injEq, Sum.inr.injEq] at heq; exact heq ▸ hc'
  · intro hc; exact ⟨c, rfl, hc⟩

@[simp] theorem none_not_mem_j0 {X : Set α} : (none : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0])

@[simp] theorem none_not_mem_j1 {Y : Set β} : (none : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1])

@[simp] theorem none_not_mem_j2 {Z : Set γ} : (none : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t2])

@[simp] theorem t1_not_mem_j0 {X : Set α} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t1])

@[simp] theorem t2_not_mem_j0 {X : Set α} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t2])

@[simp] theorem t0_not_mem_j1 {Y : Set β} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t0, t1])

@[simp] theorem t2_not_mem_j1 {Y : Set β} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1, t2])

@[simp] theorem t0_not_mem_j2 {Z : Set γ} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t0, t2])

@[simp] theorem t1_not_mem_j2 {Z : Set γ} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t1, t2])

theorem j0_inter_j0 (X X' : Set α) :
    (j0 X ∩ j0 X' : Set (Option (α ⊕ β ⊕ γ))) = j0 (X ∩ X') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, t0, Set.mem_inter_iff]

theorem j0_inter_j1 (X : Set α) (Y : Set β) :
    (j0 X ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j1, t0, t1, Set.mem_inter_iff]

theorem j0_inter_j2 (X : Set α) (Z : Set γ) :
    (j0 X ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j2, t0, t2, Set.mem_inter_iff]

theorem j0_nonempty {X : Set α} (hX : X.Nonempty) : (j0 X : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨t0 a, a, rfl, ha⟩

theorem j0_subset_j0 {X X' : Set α} :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ j0 X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact t0_mem_j0.mp (h (t0_mem_j0.mpr ha))
  · rintro h w ⟨a, rfl, ha⟩; exact t0_mem_j0.mpr (h ha)

theorem j1_inter_j1 (Y Y' : Set β) :
    (j1 Y ∩ j1 Y' : Set (Option (α ⊕ β ⊕ γ))) = j1 (Y ∩ Y') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, t1, Set.mem_inter_iff]

theorem j1_inter_j2 (Y : Set β) (Z : Set γ) :
    (j1 Y ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, j2, t1, t2, Set.mem_inter_iff]

theorem j1_nonempty {Y : Set β} (hY : Y.Nonempty) : (j1 Y : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨b, hb⟩ := hY; exact ⟨t1 b, b, rfl, hb⟩

theorem j1_subset_j1 {Y Y' : Set β} :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ j1 Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact t1_mem_j1.mp (h (t1_mem_j1.mpr hb))
  · rintro h w ⟨b, rfl, hb⟩; exact t1_mem_j1.mpr (h hb)

theorem j1_injective {Y Y' : Set β}
    (h : (j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y') : Y = Y' :=
  Set.Subset.antisymm (j1_subset_j1.mp h.subset) (j1_subset_j1.mp h.symm.subset)

theorem j2_inter_j2 (Z Z' : Set γ) :
    (j2 Z ∩ j2 Z' : Set (Option (α ⊕ β ⊕ γ))) = j2 (Z ∩ Z') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j2, t2, Set.mem_inter_iff]

theorem j2_nonempty {Z : Set γ} (hZ : Z.Nonempty) : (j2 Z : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨c, hc⟩ := hZ; exact ⟨t2 c, c, rfl, hc⟩

theorem j2_subset_j2 {Z Z' : Set γ} :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ j2 Z' ↔ Z ⊆ Z' := by
  constructor
  · intro h c hc; exact t2_mem_j2.mp (h (t2_mem_j2.mpr hc))
  · rintro h w ⟨c, rfl, hc⟩; exact t2_mem_j2.mpr (h hc)

theorem j2_injective {Z Z' : Set γ}
    (h : (j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z') : Z = Z' :=
  Set.Subset.antisymm (j2_subset_j2.mp h.subset) (j2_subset_j2.mp h.symm.subset)

end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

/-- The master neighbourhood of the three-way sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`. -/
def master3 : Set (Option (α ⊕ β ⊕ γ)) :=
  insert none (j0 V₀.master ∪ j1 V₁.master ∪ j2 V₂.master)
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

@[simp] theorem none_mem_master3 : (none : Option (α ⊕ β ⊕ γ)) ∈ master3 V₀ V₁ V₂ :=
  Set.mem_insert _ _

namespace Example62C

/-- Scott's standing assumption `∅ ∉ C`: every neighbourhood of `C` is nonempty. -/
theorem C_nonempty : ∀ X, C.mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- `b{σ} = {bσ}`: prepending a bit to a singleton. -/
theorem embBit_singleton (b : Bool) (σ : Str) : embBit b ({σ} : Set Str) = {(b :: σ : Str)} := by
  rw [embBit_eq_prepend, Example44.prepend_singleton]; rfl

end Example62C

theorem eq_master3_of_subset {W : Set (Option (α ⊕ β ⊕ γ))}
    (hsub : master3 V₀ V₁ V₂ ⊆ W) (hsub' : W ⊆ master3 V₀ V₁ V₂) : W = master3 V₀ V₁ V₂ :=
  Set.Subset.antisymm hsub' hsub

theorem j0_subset_master3 {X : Set α} (hX : V₀.mem X) :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨a, rfl, ha⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_left _ (t0_mem_j0.mpr (V₀.sub_master hX ha)))))

theorem j1_subset_master3 {Y : Set β} (hY : V₁.mem Y) :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨b, rfl, hb⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_right _ (t1_mem_j1.mpr (V₁.sub_master hY hb)))))

theorem j2_subset_master3 {Z : Set γ} (hZ : V₂.mem Z) :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨c, rfl, hc⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_right _ (t2_mem_j2.mpr (V₂.sub_master hZ hc))))

theorem master3_inter_j0 {X : Set α} (hX : V₀.mem X) :
    (master3 V₀ V₁ V₂ ∩ j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X :=
  Set.inter_eq_right.mpr (j0_subset_master3 hX)

theorem master3_inter_j1 {Y : Set β} (hY : V₁.mem Y) :
    (master3 V₀ V₁ V₂ ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y :=
  Set.inter_eq_right.mpr (j1_subset_master3 hY)

theorem master3_inter_j2 {Z : Set γ} (hZ : V₂.mem Z) :
    (master3 V₀ V₁ V₂ ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z :=
  Set.inter_eq_right.mpr (j2_subset_master3 hZ)

namespace Example62C

/-- **Example 6.2 — the shape of a `C`-neighbourhood.** Every neighbourhood of `C` is the master
`Σ* = cone []`, the terminator `{Λ} = {[]}`, a `0`-copy `0X` with `X ∈ C`, or a `1`-copy `1X`. -/
theorem memC_cases {W : Set Str} (hW : C.mem W) :
    W = Set.univ ∨ W = ({[]} : Set Str)
      ∨ (∃ X, C.mem X ∧ W = embBit false X) ∨ (∃ Y, C.mem Y ∧ W = embBit true Y) := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl cone_nil
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨cone σ', memC_cone σ', (embBit_cone false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨cone σ', memC_cone σ', (embBit_cone true σ').symm⟩))
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨{σ'}, memC_singleton σ', (embBit_singleton false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨{σ'}, memC_singleton σ', (embBit_singleton true σ').symm⟩))

/-- Prepending a bit lands back in `C`. -/
theorem memC_embBit (b : Bool) {X : Set Str} (hX : C.mem X) : C.mem (embBit b X) := by
  rw [embBit_eq_prepend]; exact Example44.memC_prepend [b] hX

/-- If `bW ∈ C` then `W ∈ C`. -/
theorem memC_embBit_inv {b : Bool} {W : Set Str} (h : C.mem (embBit b W)) : C.mem W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_cone] at hσ; rw [embBit_injective hσ]; exact memC_cone w'
  · have hmem : σ ∈ embBit b W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set Str))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_singleton] at hσ; rw [embBit_injective hσ]; exact memC_singleton w'

theorem singleton_nil_inter_embBit (b : Bool) (X : Set Str) :
    (({[]} : Set Str) ∩ embBit b X) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_embBit, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl ⟨w', heq, -⟩
  exact absurd heq (by simp)

theorem singleton_nil_ne_embBit (b : Bool) (X : Set Str) : ({[]} : Set Str) ≠ embBit b X := by
  intro h
  exact nil_not_mem_embBit (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Str) ∈ ({[]} : Set Str)))

theorem singleton_nil_ne_univ : ({[]} : Set Str) ≠ Set.univ := by
  intro h
  have hmem : ([true] : Str) ∈ ({[]} : Set Str) := h ▸ Set.mem_univ _
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

end Example62C

/-- **Example 6.2 — the three-way separated sum `D₀ + D₁ + D₂`** over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`,
under the standing assumption that no neighbourhood of any factor is empty. -/
def sum3 (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (h₂ : ∀ Z, V₂.mem Z → Z.Nonempty) : NeighborhoodSystem (Option (α ⊕ β ⊕ γ)) where
  mem W := W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
    ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)
  master := master3 V₀ V₁ V₂
  master_nonempty := ⟨none, none_mem_master3⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
    · exact subset_rfl
    · exact j0_subset_master3 hX
    · exact j1_subset_master3 hY
    · exact j2_subset_master3 hZ
  inter_mem := by
    have hne : ∀ W, (W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
        ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)) →
        (W : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
      · exact ⟨none, none_mem_master3⟩
      · exact j0_nonempty (h₀ X hX)
      · exact j1_nonempty (h₁ Y hY)
      · exact j2_nonempty (h₂ Z hZ)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Zc, hZc, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [master3_inter_j0 hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [master3_inter_j1 hY']; exact Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl⟩))
      · rw [master3_inter_j2 hZ']; exact Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl⟩))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j0 hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [j0_inter_j0] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · exact Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ0 (j0_subset_j0.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j1 hY]; exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j1_inter_j1] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · exact Or.inr (Or.inr (Or.inl ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ1 (j1_subset_j1.mp hZsub), rfl⟩))
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j2 hZc]; exact Or.inr (Or.inr (Or.inr ⟨Zc, hZc, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [Set.inter_comm, j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j2_inter_j2] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · exact Or.inr (Or.inr (Or.inr ⟨Zc ∩ Z', V₂.inter_mem hZc hZ' hZ2 (j2_subset_j2.mp hZsub), rfl⟩))

namespace Example62C

/-- `𝟙` is positive: its single neighbourhood `univ` (over the inhabited `Unit`) is nonempty. -/
theorem unitSys_nonempty : ∀ X, unitSys.mem X → X.Nonempty := by
  rintro X rfl; exact Set.univ_nonempty

/-- The right-hand side of the domain equation: the three-way sum `𝟙 + C + C`. -/
abbrev CC : NeighborhoodSystem (Option (Unit ⊕ Str ⊕ Str)) :=
  sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty

theorem sum3_mem_j1_inv {X : Set Str} (h : CC.mem (j1 X)) : C.mem X := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Y, hY, heq⟩ | ⟨Z, hZ, heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · rw [j1_injective heq]; exact hY
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1

theorem sum3_mem_j2_inv {Y : Set Str} (h : CC.mem (j2 Y)) : C.mem Y := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Z, hZ, heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t1_mem_j1.mpr hc)) t1_not_mem_j2
  · rw [j2_injective heq]; exact hY'

theorem sum3_mem_nonempty {W : Set (Option (Unit ⊕ Str ⊕ Str))} (h : CC.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨U, hU, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (unitSys_nonempty U hU)
  · exact j1_nonempty (C_nonempty Y hY)
  · exact j2_nonempty (C_nonempty Z hZ)

/-- **Example 6.2 — forward half of `C ≅ 𝟙 + C + C`.** -/
def toCC (x : C.Element) : CC.Element where
  mem W := W = master3 unitSys C C
    ∨ (W = j0 (Set.univ : Set Unit) ∧ x.mem ({[]} : Set Str))
    ∨ (∃ X, C.mem X ∧ W = j1 X ∧ x.mem (embBit false X))
    ∨ (∃ Y, C.mem Y ∧ W = j2 Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Set.univ, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨X', hX', rfl, hzF'⟩ | ⟨Y', hY', rfl, hzT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨master3_inter_j0 rfl, hzU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', master3_inter_j1 hX', hzF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', master3_inter_j2 hY', hzT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, master3_inter_j0 rfl], hzU⟩)
    · refine Or.inr (Or.inl ⟨?_, hzU⟩)
      rw [j0_inter_j0, Set.inter_self]
    · exfalso
      have hx := x.inter_mem hzU hzF'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzU hzT'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, master3_inter_j1 hX], hzF⟩))
    · exfalso
      have hx := x.inter_mem hzF hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, j1_inter_j1 X X', ?_⟩))
      · have hx := x.inter_mem hzF hzF'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzF hzF'; rwa [embBit_inter] at hx
    · exfalso
      have hx := x.inter_mem hzF hzT'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j2 hY], hzT⟩))
    · exfalso
      have hx := x.inter_mem hzT hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzT hzF'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, j2_inter_j2 Y Y', ?_⟩))
      · have hx := x.inter_mem hzT hzT'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzT hzT'; rwa [embBit_inter] at hx
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub (CC.sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain rfl := hX'; exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · refine Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl, ?_⟩))
        exact x.up_mem hzF (memC_embBit false hY') (embBit_subset.mpr (j1_subset_j1.mp hsub))
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · refine Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl, ?_⟩))
        exact x.up_mem hzT (memC_embBit true hZ') (embBit_subset.mpr (j2_subset_j2.mp hsub))

@[simp] theorem toCC_mem_j0 {x : C.Element} :
    (toCC x).mem (j0 (Set.univ : Set Unit)) ↔ x.mem ({[]} : Set Str) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · exact hz
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

@[simp] theorem toCC_mem_j1 {x : C.Element} {X : Set Str} (hX : C.mem X) :
    (toCC x).mem (j1 X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heq ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j0
    · rw [j1_injective heqj]; exact hz
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heqj ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · intro hz; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hz⟩))

@[simp] theorem toCC_mem_j2 {x : C.Element} {Y : Set Str} (hY : C.mem Y) :
    (toCC x).mem (j2 Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j0
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heqj ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1
    · rw [j2_injective heqj]; exact hz
  · intro hz; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩))

/-- **Example 6.2 — inverse half of `C ≅ 𝟙 + C + C`.** -/
def fromCC (s : CC.Element) : C.Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set Str) ∧ s.mem (j0 (Set.univ : Set Unit)))
    ∨ (∃ X, C.mem X ∧ W = embBit false X ∧ s.mem (j1 X))
    ∨ (∃ Y, C.mem Y ∧ W = embBit true Y ∧ s.mem (j2 Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl ⟨[], cone_nil.symm⟩
    · exact memC_singleton []
    · exact memC_embBit false hX
    · exact memC_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨X', hX', rfl, hsF'⟩ | ⟨Y', hY', rfl, hsT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsU hsT'; rw [j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsF⟩))
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, embBit_inter false X X', ?_⟩))
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs
        exact sum3_mem_j1_inv (s.sub hs)
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs; exact hs
    · exfalso
      have hs := s.inter_mem hsF hsT'; rw [j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsT⟩))
    · exfalso
      have hs := s.inter_mem hsT hsU'; rw [Set.inter_comm, j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsT hsF'; rw [Set.inter_comm, j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, embBit_inter true Y Y', ?_⟩))
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs
        exact sum3_mem_j2_inv (s.sub hs)
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        have hm := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · refine Or.inr (Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩))
        exact s.up_mem hsF (Or.inr (Or.inr (Or.inl ⟨X', hX', rfl⟩)))
          (j1_subset_j1.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        have hm := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩))
        exact s.up_mem hsT (Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl⟩)))
          (j2_subset_j2.mpr (embBit_subset.mp hsub))

@[simp] theorem fromCC_mem_nil {s : CC.Element} :
    (fromCC s).mem ({[]} : Set Str) ↔ s.mem (j0 (Set.univ : Set Unit)) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embBit false X')
    · exact absurd heq (singleton_nil_ne_embBit true Y')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

@[simp] theorem fromCC_mem_embF {s : CC.Element} {X : Set Str} (hX : C.mem X) :
    (fromCC s).mem (embBit false X) ↔ s.mem (j1 X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · exact absurd heq.symm (singleton_nil_ne_embBit false X)
    · rw [embBit_injective heqj]; exact hs
    · exact absurd heqj (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X hX))
  · intro hs; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hs⟩))

@[simp] theorem fromCC_mem_embT {s : CC.Element} {Y : Set Str} (hY : C.mem Y) :
    (fromCC s).mem (embBit true Y) ↔ s.mem (j2 Y) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (singleton_nil_ne_embBit true Y)
    · exact absurd heqj.symm (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X' hX'))
    · rw [embBit_injective heqj]; exact hs
  · intro hs; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩))

theorem fromCC_toCC (x : C.Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_j0.mp hs
    · exact (toCC_mem_j1 hX).mp hs
    · exact (toCC_mem_j2 hY).mp hs
  · intro hW
    rcases memC_cases (x.sub hW) with rfl | rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_j0.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (toCC_mem_j1 hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (toCC_mem_j2 hY).mpr hW⟩))

theorem toCC_fromCC (s : CC.Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embF hX).mp hs
    · exact (fromCC_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨U, hU, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · obtain rfl := hU
      exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (fromCC_mem_embF hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (fromCC_mem_embT hY).mpr hW⟩))

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|C| ≃o |𝟙 + C + C|`.** -/
def ccEquiv : C.Element ≃o CC.Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hW
      rcases memC_cases (x.sub hW) with rfl | rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_j0.mp (h _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_j1 hA).mp (h _ (Or.inr (Or.inr (Or.inl ⟨A, hA, rfl, hW⟩))))
      · exact (toCC_mem_j2 hA).mp (h _ (Or.inr (Or.inr (Or.inr ⟨A, hA, rfl, hW⟩))))
    · intro h W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, h _ hz⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, h _ hz⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, h _ hz⟩))

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `C ≅ {{Λ}} + C + C`.** Scott's domain
`C` of finite-or-infinite binary sequences is, as a domain, isomorphic to the three-way separated sum
`𝟙 + C + C`: a sequence is bottom, the finished empty sequence `Λ` (the `𝟙` summand), or begins with
`0` or `1` (the two `C` summands). -/
theorem C_domain_equation :
    C ≅ᴰ sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty :=
  ⟨ccEquiv⟩

end Example62C

end

section
variable {α β γ : Type*}

theorem j0_injective {X X' : Set α}
    (h : (j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X') : X = X' :=
  Set.Subset.antisymm (j0_subset_j0.mp h.subset) (j0_subset_j0.mp h.symm.subset)
end

namespace Example62Regular
open Language

section
variable {n : ℕ}

/-- A **total tree** over the alphabet `Σ = Fin n` (Scott's `n`-ary `±` tree): an assignment of a
`±` label (`Bool`, `true = +`) to every node, addressed by a finite selector `σ ∈ Σ*`. A tree is
*total* in Scott's sense (every node carries a genuine label), as opposed to the partial elements of
the domain `A` of `Example62A.lean` where labels may be `⊥`. -/
abbrev Tree (n : ℕ) : Type := List (Fin n) → Bool

/-- Scott's `pos : A → T`: the `±` label at the **root** of the tree (`pos(±⟨…⟩) = true/false`). -/
def pos (a : Tree n) : Bool := a []

/-- Scott's subtree selector `σ ↦ aσ`: the subtree of `a` reached by the selector `σ`. Defined so
that `(aσ)τ = a(στ)`; the `pos`-label at node `τ` of `aσ` is the label at node `στ` of `a`. -/
def select (a : Tree n) (σ : List (Fin n)) : Tree n := fun τ => a (σ ++ τ)

@[simp] theorem select_apply (a : Tree n) (σ τ : List (Fin n)) : select a σ τ = a (σ ++ τ) := rfl

/-- The `i`-th immediate subtree `aᵢ = a i` (Scott's children of the root node). -/
def child (a : Tree n) (i : Fin n) : Tree n := select a [i]

@[simp] theorem select_nil (a : Tree n) : select a [] = a := by
  funext τ; simp

@[simp] theorem pos_select (a : Tree n) (σ : List (Fin n)) : pos (select a σ) = a σ := by
  simp [pos]

/-- **Scott's language of a tree.** `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` — the selectors that land on a
`+` node. Equivalently (by `pos_select`) the set of `σ` with `a σ = true`. A `Language (Fin n)` is
just a set of words over the alphabet, exactly Scott's "language". -/
def treeLang (a : Tree n) : Language (Fin n) := {σ | a σ = true}

@[simp] theorem mem_treeLang {a : Tree n} {σ : List (Fin n)} : σ ∈ treeLang a ↔ a σ = true := Iff.rfl

/-- **Eventual periodicity (Scott).** A tree `a` is *eventually periodic* iff the set of its subtrees
`{aσ ∣ σ ∈ Σ*}` is finite. (Equivalently — by the picture — the tree is built from finitely many
distinct subtrees, so it is "ultimately periodic" along every branch.) -/
def EventuallyPeriodic (a : Tree n) : Prop := (Set.range (select a)).Finite

/-- Composing selectors: `a(στ) = (aσ)τ`. -/
theorem select_append (a : Tree n) (σ τ : List (Fin n)) :
    select a (σ ++ τ) = select (select a σ) τ := by
  funext ρ; simp [List.append_assoc]

/-- **Scott's selector recursion, step `a(iσ) = (aᵢ)σ`.** Reading the digit `i` then `σ` is the same
as descending to the `i`-th child `aᵢ` and reading `σ` there. -/
theorem select_cons (a : Tree n) (i : Fin n) (σ : List (Fin n)) :
    select a (i :: σ) = select (child a i) σ := by
  funext τ; simp [child]

/-- `L_a` is genuinely `{σ ∣ pos(aσ) = true}` as Scott writes it. -/
theorem treeLang_eq_pos (a : Tree n) : treeLang a = {σ | pos (select a σ) = true} := by
  simp only [pos_select]; rfl

/-- The label function recovers the tree from its language, so `treeLang` is **one-one**: two trees
with the same language are the same tree (a node's `±` label is recorded by whether its selector is
in the language). -/
theorem treeLang_injective : Function.Injective (treeLang (n := n)) := by
  intro a a' h
  funext σ
  have hmem : (σ ∈ treeLang a) ↔ (σ ∈ treeLang a') := by rw [h]
  simp only [mem_treeLang] at hmem
  cases ha : a σ <;> cases ha' : a' σ <;> simp_all

/-- **The subtree is the left quotient.** `L_{aσ} = σ⁻¹ L_a`: the language of the subtree reached by
reading `σ` is exactly the *left quotient* of `L_a` by `σ` (the residual / "state after reading
`σ`"). This is the heart of Scott's "`a` is the initial state, `aσ` the state after reading `σ`". -/
theorem treeLang_select (a : Tree n) (σ : List (Fin n)) :
    treeLang (select a σ) = (treeLang a).leftQuotient σ := by
  ext τ
  simp only [mem_treeLang, select_apply, Language.mem_leftQuotient]

/-- **Scott's closing claim, made precise (Example 6.2).** A tree's language `L_a` is a *regular
event* of automata theory **iff** the tree is eventually periodic. This is the Myhill–Nerode theorem
in disguise: the subtrees `aσ` are the left quotients `σ⁻¹ L_a` (`treeLang_select`), so "finitely many
subtrees" is "finitely many left quotients", which Myhill–Nerode equates with regularity. -/
theorem eventuallyPeriodic_iff_isRegular (a : Tree n) :
    EventuallyPeriodic a ↔ (treeLang a).IsRegular := by
  have hcomp : (treeLang a).leftQuotient = treeLang ∘ select a :=
    funext fun σ => (treeLang_select a σ).symm
  rw [Language.isRegular_iff_finite_range_leftQuotient, hcomp, Set.range_comp]
  exact (Set.finite_image_iff (treeLang_injective.injOn)).symm

/-- The inverse half of Scott's claim: **every regular event arises** as the language of an eventually
periodic tree. Concretely, take the tree whose root labels record membership in `L`; reading a tape
`σ` lands on the residual language `σ⁻¹ L`, of which there are finitely many exactly when `L` is
regular. -/
theorem isRegular_iff_exists_eventuallyPeriodic (L : Language (Fin n)) :
    L.IsRegular ↔ ∃ a : Tree n, EventuallyPeriodic a ∧ treeLang a = L := by
  classical
  constructor
  · intro hL
    refine ⟨fun σ => decide (σ ∈ L), ?_, ?_⟩
    · have hlang : treeLang (fun σ => decide (σ ∈ L)) = L := by
        ext σ; simp only [mem_treeLang, decide_eq_true_eq]
      rw [eventuallyPeriodic_iff_isRegular, hlang]; exact hL
    · ext σ; simp only [mem_treeLang, decide_eq_true_eq]
  · rintro ⟨a, hEP, rfl⟩
    exact (eventuallyPeriodic_iff_isRegular a).mp hEP

end

end Example62Regular
open NeighborhoodSystem ApproximableMap Example62 ExampleB

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- The master neighbourhood `{Λ} ∪ 0Δ₀ ∪ 1Δ₁` of the concrete sum. -/
def sumTokMaster (D₀ D₁ : NeighborhoodSystem Str) : Set Str :=
  insert [] (embBit false D₀.master ∪ embBit true D₁.master)

theorem embF_subset_sumTokMaster {X : Set Str} (hX : D₀.mem X) :
    embBit false X ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₀.sub_master hX)).trans (Set.subset_union_left.trans (Set.subset_insert _ _))

theorem embT_subset_sumTokMaster {Y : Set Str} (hY : D₁.mem Y) :
    embBit true Y ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₁.sub_master hY)).trans (Set.subset_union_right.trans (Set.subset_insert _ _))

theorem nil_mem_sumTokMaster : ([] : Str) ∈ sumTokMaster D₀ D₁ := Set.mem_insert _ _

theorem embF_ne_sumTokMaster {X : Set Str} : embBit false X ≠ sumTokMaster D₀ D₁ := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_sumTokMaster)

theorem embT_ne_sumTokMaster {Y : Set Str} : embBit true Y ≠ sumTokMaster D₀ D₁ := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_sumTokMaster)

theorem sumTokMaster_inter_embF {X : Set Str} (hX : D₀.mem X) :
    sumTokMaster D₀ D₁ ∩ embBit false X = embBit false X :=
  Set.inter_eq_right.mpr (embF_subset_sumTokMaster hX)

theorem sumTokMaster_inter_embT {Y : Set Str} (hY : D₁.mem Y) :
    sumTokMaster D₀ D₁ ∩ embBit true Y = embBit true Y :=
  Set.inter_eq_right.mpr (embT_subset_sumTokMaster hY)

end Exercise619
end
end DomainTheory.NeighbourhoodSystems
end
