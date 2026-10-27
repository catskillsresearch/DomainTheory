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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.transfer812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.transfer812c_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.hcore812c

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
