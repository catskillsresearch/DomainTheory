/-ai
toD0 sends an element of D₁ to the element of D₀ whose neighbourhoods are the YPseq sets for which the matching set of the second enumeration belongs to the given element. A neighbourhood of the image lies in D₀ because YPseq sets are neighbourhoods. The master is the image of the zero index once the zero conventions identify YPseq at zero with the master and the zero set of the second enumeration with its master. An intersection is the YPseq set at the index supplied by the intersection lemma on the second side. For an upward step, the covering names the larger neighbourhood as a set of the first enumeration, the cross-order transfer turns the inclusion into an inclusion of a second-enumeration set in an XPseq set, upward closure in the original element and the second covering produce an index, and the equality transfer certifies that the larger neighbourhood is the YPseq set at that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_subset_X_iff_Y_subset_XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.exists_inter_index_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_eq_Y_iff_X_eq_YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

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

/-- **Exercise 8.12(c)(vii)(5).** `toD0 : D₁.Element → D₀.Element`, the pullback filter
`{S | ∃ n, S = YPseq n ∧ y.mem (Y n)}` — exact mirror of `toD1` with the two sides' roles swapped
(`YPseq_mem`/`YPseq_zero`/`exists_inter_index_Y` for `sub`/`master_mem`/`inter_mem`;
`YPseq_subset_X_iff_Y_subset_XPseq`/`hXcover`/`hYcover`/`XPseq_eq_Y_iff_X_eq_YPseq` for `up_mem`). -/
def toD0 (y : D₁.Element) : D₀.Element where
  mem S := ∃ n, S = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ∧ y.mem (Y n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ YPseq_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n
  master_mem := ⟨0, (YPseq_zero D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
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
      (YPseq_subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne i k).mp hS1S2
    have hyXPk : y.mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k) :=
      y.up_mem hyi
        (XPseq_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne k)
        hYi_sub
    obtain ⟨j, hj⟩ := (hYcover (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k)).mp (y.sub hyXPk)
    have hYPj_eq_Xk : X k = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j :=
      (XPseq_eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne k j).mp hj
    exact ⟨j, hYPj_eq_Xk, hj ▸ hyXPk⟩

end Iso

end DomainTheory.NeighbourhoodSystems
