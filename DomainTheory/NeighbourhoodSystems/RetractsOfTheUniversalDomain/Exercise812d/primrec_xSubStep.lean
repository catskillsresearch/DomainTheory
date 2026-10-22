module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_stateIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_stateIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_stateJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xwN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xwB1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xwS
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_xwN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_xwB1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_xwS
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

theorem primrec_xSubStep : Nat.Primrec (xSubStep P₀ P₁ hDiff0 splitX hSplitX) := by
  have hn : Nat.Primrec xwN := primrec_xwN
  have hb1 : Nat.Primrec xwB1 := primrec_xwB1
  have hs : Nat.Primrec xwS := primrec_xwS
  have hidx0 : Nat.Primrec (fun w => stateIdx0 (xwS w)) := primrec_stateIdx0.comp hs
  have hidx1 : Nat.Primrec (fun w => stateIdx1 (xwS w)) := primrec_stateIdx1.comp hs
  have hjunk : Nat.Primrec (fun w => stateJunk (xwS w)) := primrec_stateJunk.comp hs
  have hinter : Nat.Primrec (fun w => P₀.inter (stateIdx0 (xwS w)) (xwN w)) :=
    (P₀.inter_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdiffidx : Nat.Primrec (fun w => hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w)) :=
    (hDiff0.diffIdx_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hemptyInter : Nat.Primrec (fun w => emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w))) :=
    (primrec_emptyInterDec P₀).comp (hidx0.pair hn)
  have hemptyDiff : Nat.Primrec
      (fun w => emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))) :=
    (primrec_emptyDiffDec P₀ hDiff0).comp (hidx0.pair hn)
  have hposIdx : Nat.Primrec
      (fun w => hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)) :=
    (hSplitX.posIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnegIdx : Nat.Primrec
      (fun w => hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)) :=
    (hSplitX.negIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdirectIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (P₀.inter (stateIdx0 (xwS w)) (xwN w)) (hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w))) :=
    primrec_selectFn hb1 hinter hdiffidx
  have hdirectEmpty : Nat.Primrec (fun w => selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w)))) :=
    primrec_selectFn hb1 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))
      (hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))) :=
    primrec_selectFn hb1 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (P₀.inter (stateIdx0 (xwS w)) (xwN w))
        (hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))
        (hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold xSubStep packState2
    simp only []

end XSubStep

end DomainTheory.NeighbourhoodSystems
