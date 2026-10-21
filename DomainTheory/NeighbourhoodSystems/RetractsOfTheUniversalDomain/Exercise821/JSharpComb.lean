/-ai
The map from the universal domain into the tree algebra of the fixed neighbourhood of an endomap a is the composite of the functorial action of the tree algebra on the subsystem projection of that fixed neighbourhood with the projection from the universal domain onto its tree algebra.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **`J : U → (D_a)§`**, symmetric to `ISharpComb`, via the subsystem projection
`(fixedNbhd_subsystem a).proj : U → D_a`. -/
noncomputable def JSharpComb (a : ApproximableMap U U) :
    ApproximableMap U (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) :=
  (dsharpMap (fixedNbhd_mem_nonempty a) U_mem_nonempty (fixedNbhd_subsystem a).proj).comp jSharp

end DomainTheory.NeighbourhoodSystems
