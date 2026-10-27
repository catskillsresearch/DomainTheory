module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPair812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitSpec812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedXY812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedY812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseq812c

@[expose] public section

@[expose] public section

/- concordance: source L5147 EXERCISE 8.12 integer presentation of U -/
-- Exercise812/affine_2.lean
namespace DomainTheory.NeighbourhoodSystems
namespace affine

open NeighborhoodSystem

end affine
end DomainTheory.NeighbourhoodSystems

/-! ### Exercise 8.12(c)–(e) (moved from Exercise_8_15 monolith) -/

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

namespace hcore
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The even-index case of `hcore`** (Exercise 8.12(c)(vi)(5)(c)(2)): for any `δ' : ℕ → Bool` and
any `n`, `genAtom combinedX δ' (2*n) = ∅ ↔ genAtom combinedY δ' (2*n) = ∅`. Direct instantiation:
de-interleave `δ'` (via (c)(1)), rewrite both `genAtom`s back to `atomPair (deinterleaveδ δ') n`'s
two sides via (b)'s `atomPair.fst_eq_genAtom`/`atomPair.snd_eq_genAtom`, then close with
`atomPair.invariant`'s clause (a) (already `Pass`, (iv)). -/
theorem even (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ' (2 * n) = ∅ ↔
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ' (2 * n) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    ← atomPair.fst_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n,
    ← atomPair.snd_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n]
  exact (atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne (deinterleaveδ δ') n).1

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The odd-index case of `hcore`** (Exercise 8.12(c)(vi)(5)(c)(3)): for any `δ' : ℕ → Bool` and
any `n`, `genAtom combinedX δ' (2*n+1) = ∅ ↔ genAtom combinedY δ' (2*n+1) = ∅`. Direct
instantiation: de-interleave `δ'` (via (c)(1)), rewrite both `genAtom`s at the odd depth
`2 * n + 1` down to the `X`-sub-step's own two sides (`(xStep … (deinterleaveδ δ' n).1).1`/`.2`) via
(b)'s odd-depth half-step identities `genAtom.combinedX_succ_eq`/`genAtom.combinedY_succ_eq` (fed
by (b)'s even-depth closed forms `atomPair.fst_eq_genAtom`/`atomPair.snd_eq_genAtom` for their own
`hn` hypotheses), then close directly with `xStep.spec_bit`'s matching-emptiness clause (already
`Pass`, (vi)(4)(c)). -/
theorem odd (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ' (2 * n + 1) = ∅ ↔
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ' (2 * n + 1) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    genAtom.combinedX_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n
      (atomPair.fst_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne (deinterleaveδ δ') n),
    genAtom.combinedY_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n
      (atomPair.snd_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne (deinterleaveδ δ') n)]
  exact (xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne (deinterleaveδ δ') n ((deinterleaveδ δ') n).1).1.symm

end AtomPair
end

end hcore
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`hcore`** (Exercise 8.12(c)(vi)(5)(c)(4), final assembly): for any `δ' : ℕ → Bool` and any
`n`, `genAtom combinedX δ' n = ∅ ↔ genAtom combinedY δ' n = ∅` — the actual `hcore` hypothesis
`Theorem88.lean`'s `transfer_dir` needs for the interleaved families `combinedX`/`combinedY`. Pure
glue: a parity case split on `n` (via `omega`, not `Nat.even_or_odd`/`Nat.even_or_odd'`, matching
this file's established choice-free-arithmetic style) matching `n = 2 * (n/2)` against (2)'s
`hcore.even` and `n = 2 * (n/2) + 1` against (3)'s `hcore.odd`. -/
theorem hcore (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ' n = ∅ ↔
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ' n = ∅ := by
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn | hn
  · rw [show n = 2 * (n / 2) from by omega]
    exact hcore.even D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne δ' (n / 2)
  · rw [show n = 2 * (n / 2) + 1 from by omega]
    exact hcore.odd D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne δ' (n / 2)

end AtomPair
end

namespace transfer
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem empty_combined {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ D₀.master | ∀ p ∈ cs, (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}.Nonempty ↔
      {y ∈ D₁.master |
        ∀ p ∈ cs, (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}.Nonempty := by
  have hc := hcore D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne
  have hc' : ∀ δ n, genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ n = ∅ ↔
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ n = ∅ :=
    fun δ n => (hc δ n).symm
  exact ⟨transfer_dir (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master
      (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master hc hn,
    transfer_dir (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master
      (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master hc' hn⟩

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem double_subset_combined (i j k : ℕ) :
    D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  have key := transfer.empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ D₀.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j) \ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j) \ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_empty_combined (i j : ℕ) :
    D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j =
        ∅ ↔
      D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j = ∅ := by
  have key := transfer.empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (cs := [(i, true), (j, true)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ D₀.master |
      ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master |
      ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem subset_combined (i j : ℕ) :
    D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ↔
      D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  have key := transfer.empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (cs := [(i, true), (j, false)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ D₀.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i) \
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i) \
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_eq_combined (i j k : ℕ)
    (hi : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ D₀.master)
    (hk : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ D₀.master) :
    combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j =
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j =
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  have h1 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i := by
    have := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
      hXmem hYmem hD₀mne hD₁mne k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedY.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k)] at this
  have h2 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    have := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
      hXmem hYmem hD₀mne hD₁mne k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedY.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k)] at this
  have h3 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
    have := transfer.double_subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right
        (combinedY.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne i)] at this
  constructor
  · intro heq
    have hki : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

end AtomPair
end

end transfer
namespace YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`YPseq n` is always `⊆ D₀.master`.** -/
theorem subset_master (n : ℕ) : YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ⊆ D₀.master := by
  apply Set.iUnion_subset
  intro δ'
  apply Set.iUnion_subset
  intro bx
  obtain ⟨hBA, hAmem⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n bx
  exact (yStep.fst_subset hD₀nomin hBA hAmem (Y n) true).trans
    ((xStep.fst_subset D₁ hD₁nomin _ _ (X n) bx).trans
      (atomPair.fst_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne (extendTruePair δ') n))

end AtomPair
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hX0 hY0 in
/-- **Exercise 8.12(c)(vii)(2), symmetric half.** `YPseq 0 = D₀.master`, by the same `SplitSpec'`
argument applied to the *second* (`Y`-)sub-step, now feeding off `XPseq.zero`'s already-computed
`D₁`-side value at the first sub-step. -/
theorem zero : YPseq D₀ D₁ hD₀nomin hD₁nomin X Y 0 = D₀.master := by
  apply Set.Subset.antisymm
    (YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne 0)
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin hAB1 hBE1 (X 0)
  have hdiff1 : D₀.master \ X 0 = ∅ := by rw [hX0]; exact Set.sdiff_self
  have h2empty1 : (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).2 = ∅ :=
    hspec1.2.2.2.1.mp hdiff1
  have hunion1 := hspec1.2.2.2.2.1
  rw [h2empty1, Set.union_empty] at hunion1
  have hAB2 : D₁.master = ∅ ↔ D₀.master = ∅ := hAB1.symm
  have hBE2 : D₀.master = ∅ ∨ D₀.mem D₀.master := Or.inr D₀.master_mem
  have hspec2 := splitChoice'_isSplitSpec D₀ hD₀nomin hAB2 hBE2 (Y 0)
  have hdiff2 : D₁.master \ Y 0 = ∅ := by rw [hY0]; exact Set.sdiff_self
  have h2empty2 : (splitChoice' D₀ hD₀nomin D₁.master D₀.master (Y 0)).2 = ∅ :=
    hspec2.2.2.2.1.mp hdiff2
  have hunion2 := hspec2.2.2.2.2.1
  rw [h2empty2, Set.union_empty] at hunion2
  have hgoal : (yStep D₀ hD₀nomin (D₀.master ∩ X 0)
      (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).1 (Y 0) true).1 ⊆
      YPseq D₀ D₁ hD₀nomin hD₁nomin X Y 0 :=
    subset.YPseq D₀ D₁ hD₀nomin hD₁nomin X Y (Fin.elim0 : Fin 0 → Bool × Bool) true
  rw [hunion1, hX0, Set.inter_self] at hgoal
  have hkey2 : D₀.master ⊆ (yStep D₀ hD₀nomin D₀.master D₁.master (Y 0) true).1 := by
    show D₀.master ⊆ (splitChoice' D₀ hD₀nomin D₁.master D₀.master (Y 0)).1
    rw [hunion2]
  exact hkey2.trans hgoal

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(3), cross-parity order fact, other mix.** `YPseq i ⊆ X j ↔
Y i ⊆ XPseq j`: the symmetric specialization of `transfer.subset_combined` at `(2i+1, 2j)`. -/
theorem subset_X_iff_Y_subset_XPseq (i j : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ X j ↔
      Y i ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  have key := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i + 1) (2 * j)
  rw [combinedX.odd, combinedX.even, combinedY.odd, combinedY.even,
    Set.inter_eq_self_of_subset_right
      (YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (hYmem i))] at key
  exact key

end Iso
end

end YPseq
open NeighborhoodSystem

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(3), cross-parity order fact (`even`/`odd` mix).** `X i ⊆ YPseq j ↔
XPseq i ⊆ Y j`: a direct specialization of `transfer.subset_combined` at the mixed indices
`(2i, 2j+1)` (`combinedX`/`combinedY` at an even and an odd index respectively), simplified by the
same `Set.inter_eq_self_of_subset_right` bookkeeping as (5)(d)'s same-parity headline facts. No new
proof machinery — `transfer.subset_combined` already holds for arbitrary index pairs. -/
theorem X_subset_YPseq_iff_XPseq_subset_Y (i j : ℕ) :
    X i ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ Y j := by
  have key := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j + 1)
  rw [combinedX.even, combinedX.odd, combinedY.even, combinedY.odd,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (hXmem i)),
    Set.inter_eq_self_of_subset_right
      (XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i)] at key
  exact key

end Iso
end

namespace XPseq
open NeighborhoodSystem

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(4), the cross-parity `embed_eq_iff` analogue.** `XPseq j = Y k ↔
X j = YPseq k`: unlike `Theorem88a.lean`'s single-enumeration `embed_eq_iff` (a direct corollary of
one `embed_subset_iff` applied twice), this two-family version packages **both** cross-parity order
facts from (vii)(3) (`X_subset_YPseq_iff_XPseq_subset_Y` at `(j, k)` and
`YPseq.subset_X_iff_Y_subset_XPseq` at `(k, j)`) via antisymmetry on each side. Needed because
`toD1`/`toD0`'s `up_mem` case must rename a `D₁`-mem (resp. `D₀`-mem) witness produced by
`hYcover`/`hXcover` as some `Y k`/`X k` back into the `XPseq`/`YPseq` "coordinates" that the filter
`x`/`y` actually testifies about. -/
theorem eq_Y_iff_X_eq_YPseq (j k : ℕ) :
    XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = Y k ↔ X j = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne j k).mpr h.subset)
      ((YPseq.subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne k j).mpr h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne j k).mp h.subset)
      ((YPseq.subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne k j).mp h.symm.subset)

end Iso
end

end XPseq
namespace combinedX
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- `combinedX i` is always `⊆ D₀.master`: at even positions it is `X (i/2)`, a `D₀.mem` set
(via `D₀.sub_master`); at odd positions it is `YPseq (i/2)`, already known `⊆ D₀.master`. -/
theorem subset_master (i : ℕ) :
    combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ D₀.master := by
  rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi
  · rw [show i = 2 * (i / 2) from by omega, combinedX.even]
    exact D₀.sub_master (hXmem (i / 2))
  · rw [show i = 2 * (i / 2) + 1 from by omega, combinedX.odd]
    exact YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (i / 2)

end AtomPair
end

end combinedX
namespace YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_eq_iff_Y_inter_eq (i j k : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      Y i ∩ Y j = Y k := by
  have key := transfer.inter_eq_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i + 1) (2 * j + 1) (2 * k + 1)
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * i + 1))
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * k + 1))
  rw [combinedX.odd, combinedX.odd, combinedX.odd, combinedY.odd, combinedY.odd,
    combinedY.odd] at key
  exact key

end AtomPair
end

end YPseq
open NeighborhoodSystem

namespace XPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem X_inter_empty_iff_XPseq_inter_empty (i j : ℕ) :
    X i ∩ X j = ∅ ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = ∅ := by
  have key := transfer.inter_empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j)
  rw [combinedX.even, combinedX.even, combinedY.even, combinedY.even,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (hXmem i)),
    Set.inter_eq_self_of_subset_right
      (XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i)] at key
  exact key

theorem X_eq_empty_iff_XPseq_eq_empty (n : ℕ) :
    X n = ∅ ↔ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = ∅ := by
  have := X_inter_empty_iff_XPseq_inter_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne n n
  rwa [Set.inter_self, Set.inter_self] at this

theorem ne_empty (n : ℕ) : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ≠ ∅ := fun h =>
  hD₀nomin.mem_ne_empty (hXmem n)
    ((X_eq_empty_iff_XPseq_eq_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne n).mpr h)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`XPseq n` is always a genuine `D₁`-neighbourhood** (never merely `∅`-or-`mem`): the actual
"other side" of `X n`. -/
theorem mem (n : ℕ) : D₁.mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) :=
  (XPseq.empty_or_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne n).resolve_left
    (XPseq.ne_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n)

end AtomPair
end

end XPseq
open NeighborhoodSystem

namespace YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_empty_iff_Y_inter_empty (i j : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = ∅ ↔
      Y i ∩ Y j = ∅ := by
  have key := transfer.inter_empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne (2 * i + 1) (2 * j + 1)
  rw [combinedX.odd, combinedX.odd, combinedY.odd, combinedY.odd,
    Set.inter_eq_self_of_subset_right
      (YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (hYmem i))] at key
  exact key

theorem Y_eq_empty_iff_YPseq_eq_empty (n : ℕ) :
    Y n = ∅ ↔ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = ∅ := by
  have := inter_empty_iff_Y_inter_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne n n
  rw [Set.inter_self, Set.inter_self] at this
  exact this.symm

theorem ne_empty (n : ℕ) : YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ≠ ∅ := fun h =>
  hD₁nomin.mem_ne_empty (hYmem n)
    ((Y_eq_empty_iff_YPseq_eq_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne n).mpr h)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`YPseq n` is always a genuine `D₀`-neighbourhood**, symmetric to `XPseq.mem`. -/
theorem mem (n : ℕ) : D₀.mem (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) :=
  (YPseq.empty_or_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne n).resolve_left
    (YPseq.ne_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n)

end AtomPair
end

end YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem X_subset_iff_XPseq_subset (i j : ℕ) :
    X i ⊆ X j ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  have key := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j)
  rw [combinedX.even, combinedX.even, combinedY.even, combinedY.even,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (hXmem i)),
    Set.inter_eq_self_of_subset_right
      (XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i)] at key
  exact key

end AtomPair
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(6), the same-family `embed_eq_iff` companion.** `X i = X j ↔
XPseq i = XPseq j`, needed by `domainIso812c`'s `map_rel_iff'`. Unlike `up_mem`'s two-*family* renaming
(needing (4)'s `XPseq.eq_Y_iff_X_eq_YPseq`), `map_rel_iff'` only ever compares two `XPseq`-indices
against each other, so the ordinary same-family pattern — `X_subset_iff_XPseq_subset` applied in
each direction, packaged via `Set.Subset.antisymm` — suffices, exactly as `Theorem88a.lean`'s own
`embed_eq_iff` (single index family). -/
theorem X_eq_iff_XPseq_eq (i j : ℕ) :
    X i = X j ↔ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne i j).mp h.subset)
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j i).mp h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne i j).mpr h.subset)
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j i).mpr h.symm.subset)

end Iso
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem X_inter_eq_iff_XPseq_inter_eq (i j k : ℕ) :
    X i ∩ X j = X k ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  have key := transfer.inter_eq_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j) (2 * k)
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * i))
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * k))
  rw [combinedX.even, combinedX.even, combinedX.even, combinedY.even, combinedY.even,
    combinedY.even] at key
  exact key

end AtomPair
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hXcover in
/-- **Exercise 8.12(c)(vii)(3), `exists_inter_index` (`D₀ → D₁` direction).** Given a `D₀`-side
witness that `X i ∩ X j` is itself a neighbourhood, `hXcover` names it as some `X m`, and (5)(d)'s
`X_inter_eq_iff_XPseq_inter_eq` pushes the same equation across to `XPseq`. Direct transcription of
`Theorem88a.lean`'s `exists_inter_index_of_dmem`. -/
theorem exists_inter_index_X {i j : ℕ} (hDij : D₀.mem (X i ∩ X j)) :
    ∃ m, X i ∩ X j = X m ∧
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        XPseq D₀ D₁ hD₀nomin hD₁nomin X Y m := by
  obtain ⟨m, hm⟩ := (hXcover (X i ∩ X j)).mp hDij
  exact ⟨m, hm, (X_inter_eq_iff_XPseq_inter_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne i j m).mp hm⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hYcover in
/-- **Exercise 8.12(c)(vii)(3), `exists_inter_index` (`D₁ → D₀` direction).** Symmetric to
`exists_inter_index_X`, using `hYcover` and `YPseq.inter_eq_iff_Y_inter_eq`. -/
theorem exists_inter_index_Y {i j : ℕ} (hDij : D₁.mem (Y i ∩ Y j)) :
    ∃ m, Y i ∩ Y j = Y m ∧
      YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y m := by
  obtain ⟨m, hm⟩ := (hYcover (Y i ∩ Y j)).mp hDij
  exact ⟨m, hm, (YPseq.inter_eq_iff_Y_inter_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne i j m).mpr hm⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

/-- **Exercise 8.12(c)(vii)(5).** `toD0 : D₁.Element → D₀.Element`, the pullback filter
`{S | ∃ n, S = YPseq n ∧ y.mem (Y n)}` — exact mirror of `toD1` with the two sides' roles swapped
(`YPseq.mem`/`YPseq.zero`/`exists_inter_index_Y` for `sub`/`master_mem`/`inter_mem`;
`YPseq.subset_X_iff_Y_subset_XPseq`/`hXcover`/`hYcover`/`XPseq.eq_Y_iff_X_eq_YPseq` for `up_mem`). -/
def toD0 (y : D₁.Element) : D₀.Element where
  mem S := ∃ n, S = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ∧ y.mem (Y n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ YPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n
  master_mem := ⟨0, (YPseq.zero D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
    hYmem hD₀mne hD₁mne hX0 hY0).symm, by rw [hY0]; exact y.master_mem⟩
  inter_mem := by
    rintro S1 S2 ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    obtain ⟨m, hYeq, hYPeq⟩ := exists_inter_index_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
      hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne hYcover (y.sub (y.inter_mem hyi hyj))
    exact ⟨m, hYPeq, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S1 S2 ⟨i, rfl, hyi⟩ hD0S2 hS1S2
    obtain ⟨k, hk⟩ := (hXcover S2).mp hD0S2
    subst hk
    have hYi_sub : Y i ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k :=
      (YPseq.subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne i k).mp hS1S2
    have hyXPk : y.mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k) :=
      y.up_mem hyi
        (XPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne k)
        hYi_sub
    obtain ⟨j, hj⟩ := (hYcover (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k)).mp (y.sub hyXPk)
    have hYPj_eq_Xk : X k = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j :=
      (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne k j).mp hj
    exact ⟨j, hYPj_eq_Xk, hj ▸ hyXPk⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

/-- **Exercise 8.12(c)(vii)(4).** `toD1 : D₀.Element → D₁.Element`, the pushforward filter
`{T | ∃ n, T = XPseq n ∧ x.mem (X n)}` — direct transcription of `Theorem88a.lean`'s `toDprimeU`.
`sub`/`master_mem`/`inter_mem` are immediate from `XPseq.mem`/`XPseq.zero`/`exists_inter_index_X`
exactly as there; `up_mem` is the one genuinely two-sided step: given `x.mem (X i)` and a `D₁.mem`
target `T₂ ⊇ XPseq i`, `hYcover` names `T₂` as some `Y k`, the cross-parity order fact
`X_subset_YPseq_iff_XPseq_subset_Y` turns `XPseq i ⊆ Y k` into `X i ⊆ YPseq k`, `x.up_mem` (on the
`D₀`-side, using `YPseq.mem`) then gives `x.mem (YPseq k)`, `hXcover` renames `YPseq k` as some
`X j`, and `XPseq.eq_Y_iff_X_eq_YPseq` finally certifies `Y k = XPseq j`. -/
def toD1 (x : D₀.Element) : D₁.Element where
  mem T := ∃ n, T = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ∧ x.mem (X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ XPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n
  master_mem := ⟨0, (XPseq.zero D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
    hYmem hD₀mne hD₁mne hX0).symm, by rw [hX0]; exact x.master_mem⟩
  inter_mem := by
    rintro T1 T2 ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hXeq, hXPeq⟩ := exists_inter_index_X D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
      hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne hXcover (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hXPeq, hXeq ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro T1 T2 ⟨i, rfl, hxi⟩ hD1T2 hT1T2
    obtain ⟨k, hk⟩ := (hYcover T2).mp hD1T2
    subst hk
    have hXi_sub : X i ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k :=
      (X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne i k).mpr hT1T2
    have hxYPk : x.mem (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k) :=
      x.up_mem hxi
        (YPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne k)
        hXi_sub
    obtain ⟨j, hj⟩ := (hXcover (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k)).mp (x.sub hxYPk)
    have hXPj_eq_Yk : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = Y k :=
      (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j k).mpr hj.symm
    exact ⟨j, hXPj_eq_Yk.symm, hj ▸ hxYPk⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

/-- **Exercise 8.12(c)(vii)(6), final assembly.** The order isomorphism `D₀.Element ≃o D₁.Element`.
`toD1`/`toD0` are mutually inverse (via (4)'s `XPseq.eq_Y_iff_X_eq_YPseq`, resolving which index in
the *other* family represents a given neighbourhood) and preserve/reflect `≤` (via
`X_eq_iff_XPseq_eq`) — direct transcription of `Theorem88a.lean`'s `domainIso`, generalized from one
shared index family (`e`/`Yidx`) to genuinely two (`X`/`XPseq` and `Y`/`YPseq`). -/
noncomputable def domainIso812c : DomainIso D₀ D₁ where
  toFun := toD1 D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne
    hXcover hYcover hX0
  invFun := toD0 D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne hXcover hYcover hX0 hY0
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      have hXeq : X k = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k n).mp hk.symm
      rw [hn, ← hXeq]
      exact hxk
    · intro hS
      obtain ⟨m, hm⟩ := (hXcover S).mp (x.sub hS)
      have hxXm : x.mem (X m) := hm ▸ hS
      obtain ⟨n, hn⟩ := (hYcover (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y m)).mp
        (XPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne m)
      have hSYPn : S = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        hm.trans ((XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
          X Y hXmem hYmem hD₀mne hD₁mne m n).mp hn)
      exact ⟨n, hSYPn, m, hn.symm, hxXm⟩
  right_inv y := by
    apply Element.ext
    intro T
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      have hXPeq : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = Y k :=
        (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne n k).mpr hk
      rw [hn, hXPeq]
      exact hyk
    · intro hT
      obtain ⟨m, hm⟩ := (hYcover T).mp (y.sub hT)
      have hyYm : y.mem (Y m) := hm ▸ hT
      obtain ⟨n, hn⟩ := (hXcover (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y m)).mp
        (YPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne m)
      have hTXPn : T = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        hm.trans (((XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne n m).mpr hn.symm).symm)
      exact ⟨n, hTXPn, m, hn.symm, hyYm⟩
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hXcover S).mp (x.sub hxS)
      have hxn : x.mem (X n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _
        (⟨n, rfl, hxn⟩ : (toD1 D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne hXcover hYcover hX0 x).mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n))
      rw [hn, (X_eq_iff_XPseq_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne n k).mpr hk]
      exact hx2k
    · intro hle T hT
      obtain ⟨n, hn, hxn⟩ := hT
      exact ⟨n, hn, hle _ hxn⟩

end Iso
end

section

/-- **Generalization of `Theorem88.lean`'s `split_fst_subset`**: a splitting operation's first
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_fst_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).1 ⊆ B :=
  Set.subset_union_left.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

/-- **Generalization of `Theorem88.lean`'s `split_snd_subset`**: a splitting operation's second
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_snd_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).2 ⊆ B :=
  Set.subset_union_right.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

end AtomPair

section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne hXcover
  hYcover hX0 hY0 in
/-- **Exercise 8.12(c)(vii)(6), headline.** `D₀ ≅ᴰ D₁`: completes Exercise 8.12(c) in full. -/
theorem isomorphic_812c : D₀ ≅ᴰ D₁ :=
  ⟨domainIso812c D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne hXcover hYcover hX0 hY0⟩
end Iso
end

end DomainTheory.NeighbourhoodSystems
end
