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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_ySubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_stateInnerC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.pcN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.pcT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_pcN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_pcT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem primrec_atomPairStep :
    Nat.Primrec (atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY) := by
  have hy : Nat.Primrec pcN := primrec_pcN
  have hst : Nat.Primrec pcT := primrec_pcT
  have hrem : Nat.Primrec (fun w => stateRemC (pcT w)) := primrec_stateRemC.comp hst
  have hs : Nat.Primrec (fun w => stateInnerC (pcT w)) := primrec_stateInnerC.comp hst
  have hb1 : Nat.Primrec (fun w => stateRemC (pcT w) % 2) := primrec_mod2.comp hrem
  have hb2 : Nat.Primrec (fun w => stateRemC (pcT w) / 2 % 2) :=
    primrec_mod2.comp (primrec_div2.comp hrem)
  have hw1 : Nat.Primrec (fun w => Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2)
      (stateInnerC (pcT w)))) := hy.pair (hb1.pair hs)
  have hs1 : Nat.Primrec (fun w => xSubStep P₀ P₁ hDiff0 splitX hSplitX
      (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2) (stateInnerC (pcT w))))) :=
    (primrec_xSubStep P₀ P₁ hDiff0 splitX hSplitX).comp hw1
  have hw2 : Nat.Primrec (fun w => Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) / 2 % 2)
      (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2) (stateInnerC (pcT w))))))) :=
    hy.pair (hb2.pair hs1)
  have hs2 : Nat.Primrec (fun w => ySubStep P₀ P₁ hDiff1 splitY hSplitY
      (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) / 2 % 2)
        (xSubStep P₀ P₁ hDiff0 splitX hSplitX
          (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2) (stateInnerC (pcT w)))))))) :=
    (primrec_ySubStep P₀ P₁ hDiff1 splitY hSplitY).comp hw2
  have hrem' : Nat.Primrec (fun w => stateRemC (pcT w) / 4) := by
    have : Nat.Primrec (fun w => stateRemC (pcT w) / 2 / 2) :=
      primrec_div2.comp (primrec_div2.comp hrem)
    exact this.of_eq fun w => by rw [Nat.div_div_eq_div_mul]
  exact (hrem'.pair hs2).of_eq fun w => by
    unfold atomPairStep packStateC
    simp only []

end AtomPairCode

end DomainTheory.NeighbourhoodSystems
