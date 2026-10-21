/-ai
The prefixing map of a finite string relates neighbourhoods X and Y of the binary-string domain when the string obtained by prepending that finite string to X is contained in Y. The master neighbourhoods are related because the prefixed master neighbourhood is still contained in the universe. The intersection law uses that the prefixed neighbourhood lies in both output neighbourhoods, so it witnesses that their intersection is a neighbourhood. Monotonicity composes the inclusion preserved by prepending with the given input and output inclusions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.SatisfiesParityEquations

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Exercise 2.16 — `x ↦ σx` is approximable.** The neighbourhood relation `X f Y ↔ σX ⊆ Y`
(confined to `B × B`). Definition 2.1: (i) `σΔ ⊆ Δ`; (ii) the prefixed cone `σX` is a common lower
bound of `Y, Y'`, witnessing `Y ∩ Y' ∈ B`; (iii) `prepend_mono` shrinks `σX'` as `X' ⊆ X`. -/
def sigmaMap (σ : Str) : ApproximableMap B B where
  rel X Y := B.mem X ∧ B.mem Y ∧ prepend σ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨B.master_mem, B.master_mem, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hpre : B.mem (prepend σ X) := memB_prepend σ hX
    have hsubInter : prepend σ X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, B.inter_mem hY hY' hpre hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', ((prepend_mono σ hX'X).trans hsub).trans hYY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
