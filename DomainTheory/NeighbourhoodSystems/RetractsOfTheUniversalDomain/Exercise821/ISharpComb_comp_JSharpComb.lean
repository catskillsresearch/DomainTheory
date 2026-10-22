module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharp_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_self_eq_aSharpInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **`I ∘ J = a§`**, when `a` is a finitary projection. -/
theorem ISharpComb_comp_JSharpComb {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    (ISharpComb a).comp (JSharpComb a) = aSharp a := by
  unfold ISharpComb JSharpComb
  rw [comp_assoc, ← comp_assoc (dsharpMap _ _ _) (dsharpMap _ _ _) jSharp, ← dsharpMap_comp,
    inj_comp_proj_eq_self ha, dsharpMap_self_eq_aSharpInner]
  exact (aSharp_eq a).symm

end DomainTheory.NeighbourhoodSystems
