/-ai
The image neighbourhood system D' consists of the sets in the image family, with master the set of all strings. The empty string witnesses that the master is the whole token set. The master belongs to the image family because it is the cone of the empty doubled encoding. Any two image sets are nested or disjoint, and every image set is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.memD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_nestedOrDisjoint

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **The image neighbourhood system `D'`.** -/
def D' : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memD' Set.univ ⟨[], Set.mem_univ _⟩
    (Or.inl ⟨[], by rw [enc_nil, cone_nil]⟩)
    D'_nestedOrDisjoint (by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact Set.subset_univ _)

end Exercise822

end DomainTheory.NeighbourhoodSystems
