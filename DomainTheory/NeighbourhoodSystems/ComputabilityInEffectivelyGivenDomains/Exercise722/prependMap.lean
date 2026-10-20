module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.concat_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.concat_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_mulElem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_emb

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- **`x ↦ σ·x`, realised as an approximable self-map on `|S|`.** Mirrors `Example44.lean`'s
`consMap`, generalised from a single bit `b` to an arbitrary word `σ`. -/
def prependMap (σ : List Bool) : ApproximableMap Ssys Ssys where
  rel Y Z := InS Y ∧ InS Z ∧ concat {σ} Y ⊆ Z
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨InS.univ, InS.univ, Set.subset_univ _⟩
  inter_right := by
    rintro Y Z Z' ⟨hY, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    have hcsub : concat {σ} Y ⊆ Z ∩ Z' := Set.subset_inter hsub hsub'
    have hne : (Z ∩ Z').Nonempty :=
      (concat_nonempty (Set.singleton_nonempty σ) hY.nonempty).mono hcsub
    exact ⟨hY, InS.inter hZ hZ' hne, hcsub⟩
  mono := by
    rintro Y Y' Z Z' ⟨_, hZ, hsub⟩ hYY' hZZ' hY' hZ'
    exact ⟨hY', hZ', (concat_mono (Set.Subset.refl _) hYY').trans (hsub.trans hZZ')⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
