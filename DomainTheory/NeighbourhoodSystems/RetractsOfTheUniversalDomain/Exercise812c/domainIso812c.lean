/-ai
domainIso812c is the order isomorphism from the elements of D₀ to the elements of D₁, sending an element by toD1 and returning by toD0. For the left inverse, a neighbourhood of the round trip is a YPseq set whose matching set of the first enumeration belongs to the original element, and the equality transfer replaces that YPseq set by the matching set; conversely the covering names the neighbourhood in the first enumeration, a second-side index is chosen for its XPseq image, and the same transfer supplies the YPseq witness. The right inverse exchanges the two families. An inequality of images reflects order by naming the neighbourhood in the first enumeration, transporting membership of its XPseq image, and using that equal XPseq images come from equal sets of the first enumeration; an inequality of elements preserves order because a neighbourhood of the image is already an XPseq set belonging to the smaller element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_eq_Y_iff_X_eq_YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.toD1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.toD0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_eq_iff_XPseq_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

/-- **Exercise 8.12(c)(vii)(6), final assembly.** The order isomorphism `D₀.Element ≃o D₁.Element`.
`toD1`/`toD0` are mutually inverse (via (4)'s `XPseq_eq_Y_iff_X_eq_YPseq`, resolving which index in
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
        (XPseq_eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k n).mp hk.symm
      rw [hn, ← hXeq]
      exact hxk
    · intro hS
      obtain ⟨m, hm⟩ := (hXcover S).mp (x.sub hS)
      have hxXm : x.mem (X m) := hm ▸ hS
      obtain ⟨n, hn⟩ := (hYcover (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y m)).mp
        (XPseq_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne m)
      have hSYPn : S = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        hm.trans ((XPseq_eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
          X Y hXmem hYmem hD₀mne hD₁mne m n).mp hn)
      exact ⟨n, hSYPn, m, hn.symm, hxXm⟩
  right_inv y := by
    apply Element.ext
    intro T
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      have hXPeq : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = Y k :=
        (XPseq_eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne n k).mpr hk
      rw [hn, hXPeq]
      exact hyk
    · intro hT
      obtain ⟨m, hm⟩ := (hYcover T).mp (y.sub hT)
      have hyYm : y.mem (Y m) := hm ▸ hT
      obtain ⟨n, hn⟩ := (hXcover (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y m)).mp
        (YPseq_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne m)
      have hTXPn : T = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        hm.trans (((XPseq_eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
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

end DomainTheory.NeighbourhoodSystems
