/-ai
The embedding of a binary word is the domain element whose neighbourhoods are the members of Scott's family that contain the word. The set of all words is such a neighbourhood. The intersection of two such neighbourhoods still contains the word, so it is nonempty and lies in the family. A larger member of the family that contains the word is again such a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_mulElem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- **Scott's embedding** `σ ↦ {X ∈ S ∣ σ ∈ X}`. This is a filter (an element of `|S|`): it contains
`Σ`, is closed under intersection (the intersection is non-empty since it still contains `σ`, so it
lies in `S` by positivity), and is upward closed. -/
def emb (σ : List Bool) : Ssys.Element where
  mem X := InS X ∧ σ ∈ X
  sub h := h.1
  master_mem := ⟨InS.univ, Set.mem_univ σ⟩
  inter_mem := by
    rintro X Y ⟨hX, hσX⟩ ⟨hY, hσY⟩
    exact ⟨InS.inter hX hY ⟨σ, hσX, hσY⟩, hσX, hσY⟩
  up_mem := by
    rintro X Y ⟨_, hσ⟩ hY hsub
    exact ⟨hY, hsub hσ⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
