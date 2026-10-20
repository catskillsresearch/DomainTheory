module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp_comp_iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **`J ∘ I = I_{(D_a)§}`**, unconditionally (no finitary/projection hypothesis on `a` needed). -/
theorem JSharpComb_comp_ISharpComb (a : ApproximableMap U U) :
    (JSharpComb a).comp (ISharpComb a) =
      idMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) := by
  unfold JSharpComb ISharpComb
  rw [comp_assoc, ← comp_assoc jSharp iSharp (dsharpMap _ _ _), jSharp_comp_iSharp, idMap_comp,
    ← dsharpMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, dsharpMap_id]

end DomainTheory.NeighbourhoodSystems
