/-ai
For a set of points of Cantor space other than the whole space, elementOfOpen is the element of V whose members are the sets of natural numbers corresponding to a member of the dual of the ideal of coordinate-generated subsets of that set. The field sub shows each such set is admissible for V: the witnessing Cantor set is nonempty, because the ideal excludes the whole space and therefore the dual excludes the empty set, and correspondence carries generation by the generators together with nonemptiness. The master is the whole Cantor space, present in the dual because the empty set is in the ideal, and corresponding to truth. An intersection is witnessed by the intersection of the two Cantor sets, using closure of the ideal under union and preservation of correspondence under intersection. An upward step from a member to a larger admissible set uses a formula for that larger set; its Cantor-space evaluation corresponds to it, the ideal is downward closed so the dual is upward closed, and correspondence transports the inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.evalSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Corresponds
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.nonempty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.univ_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.not_empty_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.inter_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.up_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.empty_mem_idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.univ_not_mem_idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.union_mem_idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.down_mem_idealOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- **`8.13(c4)`, the headline connection.** Every open `O ≠ Set.univ` of Cantor space `2^ℕ`
determines a genuine element of `V` (hence of `U`, via `exercise813a`) — the proper filter "dual"
to the ideal of clopens inside `O`, transported to `ℕ`-clopens via `Corresponds`. This is the
precise sense in which `8.13(a)`'s filter-domain representation of `U` connects with the
(non-`univ`, and per Scott's remark, morally non-empty) open subsets of Cantor space. -/
def elementOfOpen {O : Set (ℕ → Bool)} (hO : O ≠ Set.univ) : V.Element where
  mem X := ∃ Y, Y ∈ dualFilter (idealOf O) ∧ Corresponds X Y
  sub := by
    rintro X ⟨Y, hY, hCorr⟩
    have hYne : Y ≠ ∅ := fun hYe =>
      not_empty_mem_dualFilter (univ_not_mem_idealOf hO) (hYe ▸ hY)
    exact V_mem_iff_generatedBy.mpr ⟨hCorr.generatedBy_left,
      hCorr.nonempty_iff.mpr (Set.nonempty_iff_ne_empty.mpr hYne)⟩
  master_mem := ⟨Set.univ, univ_mem_dualFilter (empty_mem_idealOf O), .top, rfl, rfl⟩
  inter_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁, hC₁⟩ ⟨Y₂, hY₂, hC₂⟩
    exact ⟨Y₁ ∩ Y₂,
      inter_mem_dualFilter (fun Y hY Z hZ => union_mem_idealOf hY hZ) hY₁ hY₂, hC₁.inter hC₂⟩
  up_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁, hC₁⟩ hX₂mem hX₁X₂
    obtain ⟨hX₂gen, -⟩ := V_mem_iff_generatedBy.mp hX₂mem
    obtain ⟨ψ, hψ⟩ := generatedBy_iff_exists_evalSet.mp hX₂gen
    have hC₂ : Corresponds X₂ (evalSet' ψ) := ⟨ψ, hψ, rfl⟩
    refine ⟨evalSet' ψ,
      up_mem_dualFilter (fun Y hY Z hZg hZY => down_mem_idealOf hY hZg hZY) hY₁
        hC₂.generatedBy_right ((hC₁.subset_iff hC₂).mp hX₁X₂),
      hC₂⟩

end DomainTheory.NeighbourhoodSystems
