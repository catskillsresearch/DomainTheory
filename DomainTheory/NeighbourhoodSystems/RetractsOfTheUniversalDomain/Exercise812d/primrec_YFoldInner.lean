/-ai
The inner Y-fold, read on a packed triple of depth, branch, and stage, is primitive recursive.

Reassembling the three components into the pair expected by the paired fold is primitive recursive. Composing the primitive-recursive paired fold and rewriting by the equation of the inner fold with its paired form gives the claim.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_YFoldInnerPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_eq_pair

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
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

theorem primrec_YFoldInner : Nat.Primrec
    (fun t : ℕ => YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2) := by
  have h1 : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.left)
  have h2 : Nat.Primrec (fun t : ℕ => Nat.pair
      (Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) t.unpair.2) :=
    h1.pair Nat.Primrec.right
  exact ((primrec_YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
    h2).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
      exact (YFoldInner_eq_pair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2).symm

end YPseqCode

end DomainTheory.NeighbourhoodSystems
