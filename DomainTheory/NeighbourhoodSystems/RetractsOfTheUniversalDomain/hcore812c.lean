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

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems
