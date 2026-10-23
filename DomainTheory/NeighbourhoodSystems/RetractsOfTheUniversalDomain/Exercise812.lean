module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`2^k ℕ + ℓ`** (for `ℓ < 2^k`): the residue class of `ℓ` modulo `2^k`. Automatically `∅` when
`ℓ ≥ 2^k` (no `n` can leave a remainder that large), matching Scott's side condition `ℓ < 2^k`
without needing to bake it into the definition. -/
def affine (k ℓ : ℕ) : Set ℕ := {n : ℕ | n % 2 ^ k = ℓ}

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem mem_affine {k ℓ n : ℕ} : n ∈ affine k ℓ ↔ n % 2 ^ k = ℓ := Iff.rfl

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace affine

open NeighborhoodSystem


theorem nonempty {k ℓ : ℕ} (hℓ : ℓ < 2 ^ k) : (affine k ℓ).Nonempty :=
  ⟨ℓ, Nat.mod_eq_of_lt hℓ⟩

end affine
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- The union of the residue classes `affine k ℓ` for `ℓ < 2^k` with `m.testBit ℓ = true`. Every
finite union of `affine`-sets sharing the *same* level `k` is of this form for a unique `m`
(`Finset.range (2^k)` residues partition `ℕ`, unlike arbitrary rational intervals), so a single
natural number `m` replaces the `List` bookkeeping `Definition87.lean` needs for `𝒰`. -/
def levelSet (k m : ℕ) : Set ℕ := {n : ℕ | m.testBit (n % 2 ^ k) = true}

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem mem_levelSet {k m n : ℕ} : n ∈ levelSet k m ↔ m.testBit (n % 2 ^ k) = true :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem


theorem inter_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ ∩ levelSet k m₂ = levelSet k (m₁ &&& m₂) := by
  ext n; simp [levelSet, Nat.testBit_and]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem


theorem nonempty_iff {k m : ℕ} :
    (levelSet k m).Nonempty ↔ ∃ ℓ < 2 ^ k, m.testBit ℓ = true := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n % 2 ^ k, Nat.mod_lt n (by positivity), hn⟩
  · rintro ⟨ℓ, hℓ, hm⟩
    exact ⟨ℓ, by rw [mem_levelSet, Nat.mod_eq_of_lt hℓ]; exact hm⟩

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem


theorem union_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ ∪ levelSet k m₂ = levelSet k (m₁ ||| m₂) := by
  ext n; simp [levelSet, Nat.testBit_or]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem


/-- `levelSet k m` is exactly the union of `affine k ℓ` over `ℓ` with `m.testBit ℓ`. -/
theorem eq_biUnion (k m : ℕ) :
    levelSet k m = ⋃ ℓ ∈ (Finset.range (2 ^ k)).filter (fun ℓ => m.testBit ℓ), affine k ℓ := by
  ext n
  simp only [mem_levelSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, mem_affine,
    exists_prop]
  constructor
  · intro h; exact ⟨n % 2 ^ k, ⟨Nat.mod_lt n (by positivity), h⟩, rfl⟩
  · rintro ⟨ℓ, ⟨-, hm⟩, rfl⟩; exact hm

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace affine

open NeighborhoodSystem


/-- `affine k ℓ` itself is the singleton-bitmask `levelSet`. -/
theorem eq_levelSet (k ℓ : ℕ) : affine k ℓ = levelSet k (2 ^ ℓ) := by
  ext n
  simp [mem_affine, mem_levelSet, Nat.testBit_two_pow, eq_comm]

end affine
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Re-express a level-`k` bitmask `m` at a finer level `k' ≥ k`: residue `r` (mod `2^k'`) is
included iff `r`'s coarser residue `r % 2^k` was. Built via `Nat.equivBitIndices` (the bijection
`ℕ ≃ Finset ℕ` sending `n` to its set bits) rather than raw shifting arithmetic. -/
def upsample (k k' m : ℕ) : ℕ :=
  ∑ r ∈ (Finset.range (2 ^ k')).filter (fun r => m.testBit (r % 2 ^ k)), 2 ^ r

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace testBit

open NeighborhoodSystem

theorem upsample {k k' m r : ℕ} (hr : r < 2 ^ k') :
    (_root_.DomainTheory.NeighbourhoodSystems.upsample k k' m).testBit r ↔ m.testBit (r % 2 ^ k) := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.upsample
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow,
    Finset.mem_filter, Finset.mem_range]
  simp [hr]

end testBit
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem

/-- `levelSet 0 1 = ℕ`: at level `0` there is a single residue class (everything is `≡ 0 mod 1`),
and `1` (bit `0` set) selects it. This is `V`'s master neighbourhood. -/
theorem zero_one : levelSet 0 1 = Set.univ := by
  ext n; simp [levelSet, Nat.mod_one]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem

/-- **`upsample` preserves the set `levelSet` represents.** -/
theorem upsample {k k' m : ℕ} (hk : k ≤ k') : levelSet k' (_root_.DomainTheory.NeighbourhoodSystems.upsample k k' m) = levelSet k m := by
  ext n
  simp only [mem_levelSet]
  rw [testBit.upsample (Nat.mod_lt n (by positivity)),
    Nat.mod_mod_of_dvd n (pow_dvd_pow 2 hk)]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem

/-- **`levelSet` is closed under intersection, unconditionally** (unlike `Definition87.lean`'s `U`,
which genuinely needs a consistency hypothesis): upsample both masks to the common level
`max k₁ k₂` and take the bitwise `AND`. -/
theorem inter (k₁ m₁ k₂ m₂ : ℕ) :
    levelSet k₁ m₁ ∩ levelSet k₂ m₂
      = levelSet (max k₁ k₂) (_root_.DomainTheory.NeighbourhoodSystems.upsample k₁ (max k₁ k₂) m₁ &&& _root_.DomainTheory.NeighbourhoodSystems.upsample k₂ (max k₁ k₂) m₂) := by
  rw [← levelSet.upsample (le_max_left k₁ k₂) (m := m₁), ← levelSet.upsample (le_max_right k₁ k₂) (m := m₂)]
  ext n
  simp only [mem_levelSet, Set.mem_inter_iff, Nat.testBit_and, Bool.and_eq_true]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Exercise 8.12's `V`**: the neighbourhood system over `ℕ` whose neighbourhoods are the
non-empty finite unions of residue classes `2^k ℕ + ℓ` (`ℓ < 2^k`). Bookkeeping-free via
`levelSet`: every finite union of `affine`-sets — even at *different* levels `kᵢ` — refines
(`levelSet.upsample`) to a single common level, so `V.mem X := ∃ k m, X = levelSet k m` already
captures every such union (`V_mem_iff_finiteUnion` below makes this precise). Closure under
intersection needs no consistency hypothesis (`levelSet.inter`), mirroring `Example78.lean`'s `PN`
rather than `Definition87.lean`'s `U`. -/
def V : NeighborhoodSystem ℕ where
  mem X := ∃ k m, X = levelSet k m ∧ X.Nonempty
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := ⟨0, 1, levelSet.zero_one.symm, Set.univ_nonempty⟩
  inter_mem := by
    rintro X Y Z ⟨k₁, m₁, rfl, -⟩ ⟨k₂, m₂, rfl, -⟩ ⟨k₃, m₃, rfl, hZne⟩ hZsub
    exact ⟨max k₁ k₂, upsample k₁ (max k₁ k₂) m₁ &&& upsample k₂ (max k₁ k₂) m₂,
      levelSet.inter k₁ m₁ k₂ m₂, hZne.mono hZsub⟩
  sub_master := by rintro X _; exact Set.subset_univ X

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`V` is closed under binary union**, as long as the result is non-empty — mirrors
`Definition87.lean`'s `U_union_mem`, needed to reassemble Scott's literal finite unions. -/
theorem V_union_mem {X Y : Set ℕ} (hX : X = ∅ ∨ V.mem X) (hY : Y = ∅ ∨ V.mem Y) :
    X ∪ Y = ∅ ∨ V.mem (X ∪ Y) := by
  rcases hX with rfl | hX
  · simpa using hY
  rcases hY with rfl | hY
  · simpa using Or.inr hX
  obtain ⟨k₁, m₁, rfl, hXne⟩ := hX
  obtain ⟨k₂, m₂, rfl, -⟩ := hY
  have heq : levelSet k₁ m₁ ∪ levelSet k₂ m₂
      = levelSet (max k₁ k₂) (upsample k₁ (max k₁ k₂) m₁ ||| upsample k₂ (max k₁ k₂) m₂) := by
    rw [← levelSet.union_same_level, levelSet.upsample (le_max_left k₁ k₂),
      levelSet.upsample (le_max_right k₁ k₂)]
  exact Or.inr ⟨max k₁ k₂, _, heq, hXne.mono Set.subset_union_left⟩

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`V` is closed under finite (`Fintype`-indexed) unions**, as long as the result is
non-empty — mirrors `Definition87.lean`'s `U_iUnion_mem` verbatim. -/
theorem V_iUnion_mem {ι : Type*} [Fintype ι] {f : ι → Set ℕ} (hf : ∀ i, f i = ∅ ∨ V.mem (f i))
    (hne : (⋃ i, f i).Nonempty) : V.mem (⋃ i, f i) := by
  classical
  have hstep : ∀ s : Finset ι, (⋃ i ∈ s, f i) = ∅ ∨ V.mem (⋃ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact V_union_mem (hf i) ih
  have hall : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [hall] at hne ⊢
  exact (hstep Finset.univ).resolve_left hne.ne_empty

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`V.mem` literally matches Scott's "non-empty finite unions of `2^k ℕ + ℓ`, `ℓ < 2^k`"** —
reconciles the bookkeeping-free `levelSet` encoding with Exercise 8.12's literal description,
mirroring `Definition87.lean`'s `U_mem_iff_scott`. -/
theorem V_mem_iff_finiteUnion {X : Set ℕ} :
    V.mem X ↔
      ∃ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.2 < 2 ^ p.1) ∧ X = ⋃ p ∈ F, affine p.1 p.2 ∧ X.Nonempty := by
  constructor
  · rintro ⟨k, m, rfl, hne⟩
    refine ⟨(Finset.range (2 ^ k)).filter (fun ℓ => m.testBit ℓ) |>.image (fun ℓ => (k, ℓ)), ?_, ?_, hne⟩
    · rintro ⟨k', ℓ⟩ hp
      obtain ⟨ℓ', hℓ', heq⟩ := Finset.mem_image.mp hp
      obtain ⟨hlt, -⟩ := Finset.mem_filter.mp hℓ'
      simp only [Finset.mem_range] at hlt
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      exact hlt
    · rw [levelSet.eq_biUnion]
      ext n
      simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
        exists_prop, exists_exists_and_eq_and]
  · rintro ⟨F, hbound, rfl, hne⟩
    have hf : ∀ p : F, affine p.1.1 p.1.2 = ∅ ∨ V.mem (affine p.1.1 p.1.2) :=
      fun ⟨p, hp⟩ => Or.inr ⟨p.1, 2 ^ p.2, affine.eq_levelSet p.1 p.2,
        affine.eq_levelSet p.1 p.2 ▸ affine.nonempty (hbound p hp)⟩
    have hrw : (⋃ p ∈ F, affine p.1 p.2) = ⋃ p : F, affine p.1.1 p.1.2 := by
      ext n; simp only [Set.mem_iUnion, exists_prop, Subtype.exists]
    rw [hrw] at hne ⊢
    exact V_iUnion_mem hf hne

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812 : ∀ {X : Set Nat},
  Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Nat DomainTheory.NeighbourhoodSystems.V X)
    (∃ (F : Finset (Prod Nat Nat)),
      And
        (∀ (p : Prod Nat Nat),
          @Membership.mem (Prod Nat Nat) (Finset (Prod Nat Nat))
              (@SetLike.instMembership (Finset (Prod Nat Nat)) (Prod Nat Nat) (@Finset.instSetLike (Prod Nat Nat))) F
              p →
            @LT.lt Nat instLTNat (@Prod.snd Nat Nat p)
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Prod.fst Nat Nat p)))
        (And
          (@Eq (Set Nat) X
            (⋃ (p : Prod Nat Nat),
              ⋃ (_ :
                @Membership.mem (Prod Nat Nat) (Finset (Prod Nat Nat))
                  (@SetLike.instMembership (Finset (Prod Nat Nat)) (Prod Nat Nat) (@Finset.instSetLike (Prod Nat Nat)))
                  F p),
                DomainTheory.NeighbourhoodSystems.affine (@Prod.fst Nat Nat p) (@Prod.snd Nat Nat p)))
          (@Set.Nonempty Nat X))) :=
  @DomainTheory.NeighbourhoodSystems.V_mem_iff_finiteUnion

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **Scott's remark after Definition 8.7, transplanted to `V`**: every `V`-neighbourhood splits
into two disjoint proper `V`-neighbourhoods. Refine to one level finer via `upsample`, which
duplicates every set bit `ℓ` of `m` into a matching pair `(ℓ, ℓ + 2^k)`; peeling off *one*
representative bit `ℓ₀` (witnessing `X`'s non-emptiness) leaves its twin `ℓ₀ + 2^k` behind, so the
"rest" is guaranteed non-empty regardless of how many other bits `m` had. -/
theorem V_no_minimal {X : Set ℕ} (hX : V.mem X) :
    ∃ Y Z : Set ℕ, V.mem Y ∧ V.mem Z ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ Y ≠ X ∧ Z ≠ X := by
  obtain ⟨k, m, rfl, hne⟩ := hX
  obtain ⟨ℓ₀, hℓ₀, hbit⟩ := levelSet.nonempty_iff.mp hne
  have hstep : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
  have hℓ₀2 : ℓ₀ < 2 ^ (k + 1) := by omega
  have hℓ₀' : ℓ₀ + 2 ^ k < 2 ^ (k + 1) := by omega
  set M := upsample k (k + 1) m with hM
  have hXM : levelSet k m = levelSet (k + 1) M := (levelSet.upsample (Nat.le_succ k)).symm
  have hMℓ₀ : M.testBit ℓ₀ = true := by
    rw [hM, testBit.upsample hℓ₀2, Nat.mod_eq_of_lt hℓ₀]; exact hbit
  have hMℓ₀' : M.testBit (ℓ₀ + 2 ^ k) = true := by
    rw [hM, testBit.upsample hℓ₀', Nat.add_mod_right, Nat.mod_eq_of_lt hℓ₀]; exact hbit
  set Y := levelSet (k + 1) (2 ^ ℓ₀) with hYdef
  set Z := levelSet (k + 1) (M ^^^ 2 ^ ℓ₀) with hZdef
  have hYmem : V.mem Y := ⟨k + 1, 2 ^ ℓ₀, rfl, levelSet.nonempty_iff.mpr ⟨ℓ₀, hℓ₀2, by simp⟩⟩
  have hZmem : V.mem Z := ⟨k + 1, M ^^^ 2 ^ ℓ₀, rfl,
    levelSet.nonempty_iff.mpr ⟨ℓ₀ + 2 ^ k, hℓ₀', by
      rw [Nat.testBit_xor, hMℓ₀']; simp⟩⟩
  have hInter : Y ∩ Z = ∅ := by
    rw [hYdef, hZdef, levelSet.inter_same_level]
    ext n
    simp only [mem_levelSet, Set.mem_empty_iff_false, iff_false, Nat.testBit_and, Bool.and_eq_true]
    rintro ⟨h1, h2⟩
    have hpos : n % 2 ^ (k + 1) = ℓ₀ := by
      by_contra hne'
      rw [Nat.testBit_two_pow] at h1
      exact hne' (of_decide_eq_true h1).symm
    rw [hpos, Nat.testBit_xor, hMℓ₀] at h2
    simp at h2
  have hUnion : Y ∪ Z = levelSet k m := by
    rw [hYdef, hZdef, levelSet.union_same_level, hXM]
    congr 1
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_xor]
    rcases eq_or_ne i ℓ₀ with rfl | hi
    · simp [hMℓ₀]
    · simp [Ne.symm hi]
  have hYne : Y.Nonempty := (levelSet.nonempty_iff (k := k + 1) (m := 2 ^ ℓ₀)).mpr ⟨ℓ₀, hℓ₀2, by simp⟩
  have hZne : Z.Nonempty := (levelSet.nonempty_iff (k := k + 1) (m := M ^^^ 2 ^ ℓ₀)).mpr
    ⟨ℓ₀ + 2 ^ k, hℓ₀', by
      rw [Nat.testBit_xor, hMℓ₀']; simp⟩
  refine ⟨Y, Z, hYmem, hZmem, hInter, hUnion, ?_, ?_⟩
  · intro hEq
    apply hZne.ne_empty
    have hZsub : Z ⊆ Y := by rw [hEq]; exact hUnion ▸ Set.subset_union_right
    rw [← hInter, Set.inter_eq_right.mpr hZsub]
  · intro hEq
    apply hYne.ne_empty
    have hYsub : Y ⊆ Z := by rw [hEq]; exact hUnion ▸ Set.subset_union_left
    rw [← hInter, Set.inter_eq_left.mpr hYsub]

end DomainTheory.NeighbourhoodSystems
