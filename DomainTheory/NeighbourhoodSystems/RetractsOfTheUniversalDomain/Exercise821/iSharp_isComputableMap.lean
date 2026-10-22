/-ai
The embedding of the tree algebra of the universal domain into the universal domain is a computable map.

This is the computability clause for that embedding in the projection pair chosen by the strong form of Theorem 8.8.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


theorem iSharp_isComputableMap :
    ComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      UComputablePresentation iSharp :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.2.1

end DomainTheory.NeighbourhoodSystems
