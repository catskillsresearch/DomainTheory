/-ai
The map from the tree algebra of the fixed neighbourhood of an endomap a into the universal domain is the composite of the embedding of the tree algebra of the universal domain with the functorial action of the tree algebra on the subsystem injection of that fixed neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **`I : (D_a)§ → U`**, transporting `iSharp` through `dsharpMap`'s action on the subsystem
injection `(fixedNbhd_subsystem a).inj : D_a → U`. -/
noncomputable def ISharpComb (a : ApproximableMap U U) :
    ApproximableMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) U :=
  iSharp.comp (dsharpMap U_mem_nonempty (fixedNbhd_mem_nonempty a) (fixedNbhd_subsystem a).inj)

end DomainTheory.NeighbourhoodSystems
