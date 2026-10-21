/-ai
The first component of the atom pair of a sign sequence at depth n equals the Boolean atom, over the interleaved family and the interleaved sign, of depth 2n, taken relative to the master of the first system.

At depth zero both sides are that master. At a successor, the inductive hypothesis and the successor identity for the interleaved atom rewrite the odd depth, the closed form for the first output of the Y-step rewrites the first component of the successor pair, and the doubling 2(n + 1) = 2n + 2 together with the odd-index clauses of the interleaved family and sign complete the identification.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_succ'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_fst_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_combinedX_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Headline closed form, `α`-side** (Exercise 8.12(c)(vi)(5)(b)): `atomPair δ n`'s `α`-side
coincides with `genAtom` over the interleaved family `combinedX` at the doubled depth `2 * n`.
Proved by induction on `n`, each step performing the two half-step rewrites
`genAtom_combinedX_succ_eq` (`X`-sub-step half, elementary) then `yStep_fst_succ_eq` ((vi)(5)(a)'s
`Y`-sub-step closed form) — mirrors `Theorem88.lean`'s one-line `atomU_eq_genAtom`, just with each
level's step split into the two named half-steps. -/
theorem atomPair_fst_eq_genAtom (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 =
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom_combinedX_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne δ n hIH
      have hstep := yStep_fst_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne δ n (δ n).2
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPair_succ_eq, hstep, h2, genAtom_succ', combinedδ_odd, combinedX_odd, hodd]

end AtomPair

end DomainTheory.NeighbourhoodSystems
