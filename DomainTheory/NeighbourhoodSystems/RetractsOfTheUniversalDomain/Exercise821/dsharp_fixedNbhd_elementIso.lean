/-ai
For a finitary projection a of the universal domain, the elements of the tree algebra of the fixed neighbourhood of a are order-isomorphic to the elements of the universal domain fixed by the sharp of a. The isomorphism is the element isomorphism of the projection pair formed by the transported embedding and projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb_comp_ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb_comp_JSharpComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Exercise 8.21(c) (Scott 1981, PRG-19).** For a finitary projection `a` of `U`, the tree
algebra `(D_a)§` of `D_a := fixedNbhd a` is order-isomorphic to `a§`'s own fixed-point domain —
Scott's headline isomorphism `D_{a§} ≅ (D_a)§`. -/
noncomputable def dsharp_fixedNbhd_elementIso {a : ApproximableMap U U}
    (ha : FinitaryProjection a) :
    (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)).Element ≃o
      {y : U.Element // (aSharp a).toElementMap y = y} :=
  elementIsoOfProjectionPair (ISharpComb a) (JSharpComb a) (JSharpComb_comp_ISharpComb a)
    (ISharpComb_comp_JSharpComb ha).symm

end DomainTheory.NeighbourhoodSystems
