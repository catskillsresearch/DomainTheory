/-ai
The catamorphism of the leaf embedding and the pairing is the identity on the tree algebra.

Both inequalities are comparisons of relations. A graph-related pair is identity-related, and an identity-related pair is graph-related.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.grel_inSharp_pairSharp_imp_idMap_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.idMap_rel_imp_grel_inSharp_pairSharp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- **`gMap in pair = I_{D§}`**: the catamorphism instantiated at `u := in`, `v := pair` (the tree
algebra's own structure maps) is the identity on `D§`. -/
theorem gMap_inSharp_pairSharp_eq_idMap :
    gMap (inSharpMap hD) (pairSharpMap hD) hD = idMap (Dsharp D hD) := by
  apply le_antisymm
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact grel_inSharp_pairSharp_imp_idMap_rel h
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact idMap_rel_imp_grel_inSharp_pairSharp h.1 h.2.1 h.2.2

end DomainTheory.NeighbourhoodSystems
