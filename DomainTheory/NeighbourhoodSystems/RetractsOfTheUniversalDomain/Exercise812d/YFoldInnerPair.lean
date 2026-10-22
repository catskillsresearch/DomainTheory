module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldStep

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

/-- **Auxiliary single-argument-`z` repackaging of `YFoldInner`**, matching `Nat.Primrec.prec`'s
own shape exactly (`z := nb` used *directly*, with no `Nat.pair`/`unpair` round-trip needed for
`rfl` to see through) — mirroring `XFold`'s own successful pattern, where `z := n` needed no
repackaging at all since `XFold` has only one "held-fixed" parameter. `YFoldInner` needs *two*
(`n`, `bx`), so this auxiliary exists purely to keep `primrec_YFoldInner`'s own proof cheap: the
`Nat.pair`/`unpair` round-trip (`pair_unpair`, *not* definitionally `rfl` — it needs the `Nat.sqrt`
case split) is pushed into `unpair_pair_fst`/`_snd`-driven `simp`, not the kernel's `whnf`. -/
noncomputable def YFoldInnerPair (nb N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hUnion0 (Nat.pair nb (Nat.pair i acc)))

end YPseqCode

end DomainTheory.NeighbourhoodSystems
