module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_fst_union_step

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **8.12(d)(4)(c)(ii): classical covering induction.** The classical `atomPairG` pieces at depth
`n`, ranged over all sign-histories `δ' : Fin n → Bool × Bool` (padded to `ℕ → Bool × Bool` via
`extendTruePair`), cover `D₀.master`. Induction on `n` chaining `atomPairG_fst_union_step` at every
step; base case `n = 0` is trivial (`atomPairG _ 0 = (D₀.master, D₁.master)`, one piece covering
itself). The successor step extends a covering history `δ'₀ : Fin n → Bool × Bool` for `z` by one
more `(b1, b2) : Bool × Bool` bit via the usual `Function.update`-based device (`extendTruePair
δ'₀` updated at `n`, then `restrictFinPair`'d back down to `Fin (n + 1) → Bool × Bool`; mirrors
`Exercise812c.lean`'s `xStep_spec_bit`/`yStep_fst_eq_inter_YPseq` proofs), picking whichever of the
four `atomPairG_fst_union_step` branches `z` actually landed in. -/
theorem atomPairG_master_covered (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ δ' : Fin n → Bool × Bool,
      z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') n).1 := by
  induction n with
  | zero => exact fun z hz => ⟨Fin.elim0, hz⟩
  | succ n ih =>
    intro z hz
    obtain ⟨δ'₀, hδ'₀⟩ := ih z hz
    have hcover := atomPairG_fst_union_step D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ'₀) n
    set A := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).2 with hBdef
    have step : ∀ b1 b2 : Bool,
        z ∈ (yStepG splitY (xStepG splitX A B (X n) b1).1 (xStepG splitX A B (X n) b1).2
          (Y n) b2).1 →
        ∃ δ' : Fin (n + 1) → Bool × Bool,
          z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') (n + 1)).1 := by
      intro b1 b2 hz'
      set δ'' := Function.update (extendTruePair δ'₀) n (b1, b2) with hδ''def
      refine ⟨restrictFinPair δ'' (n + 1), ?_⟩
      have hagree : ∀ i < n + 1, extendTruePair (restrictFinPair δ'' (n + 1)) i = δ'' i :=
        fun i hi => extendTruePair_restrictFinPair_agree δ'' (n + 1) i hi
      rw [atomPairG_congr D₀ D₁ splitY splitX X Y hagree, atomPairG_succ_eq]
      have hagreeN : ∀ i < n, δ'' i = extendTruePair δ'₀ i := by
        intro i hi
        simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
      have hbit : δ'' n = (b1, b2) := by simp [hδ''def]
      rw [atomPairG_congr D₀ D₁ splitY splitX X Y hagreeN, hbit]
      exact hz'
    rw [← hcover] at hδ'₀
    simp only [Set.mem_union] at hδ'₀
    rcases hδ'₀ with (h1 | h2) | (h3 | h4)
    · exact step true true h1
    · exact step true false h2
    · exact step false true h3
    · exact step false false h4

end AtomPairGen

end DomainTheory.NeighbourhoodSystems
