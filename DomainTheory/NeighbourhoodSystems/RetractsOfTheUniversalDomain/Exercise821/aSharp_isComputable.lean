/-ai
If an endomap a of the universal domain is computable, then its sharp is computable.

The composite of the leaf embedding with a is computable because both factors are. The inner sharp is then computable by the computability of the catamorphism, using computability of pairing. Composing on either side with the computable projection and embedding of the tree algebra yields computability of the sharp.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.iSharp_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp_isComputableMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}











/-- **`a§` is computable whenever `a` is.** -/
theorem aSharp_isComputable {a : ApproximableMap U U}
    (ha : IsComputableMap UComputablePresentation UComputablePresentation a) :
    IsComputableMap UComputablePresentation UComputablePresentation (aSharp a) := by
  have hu : IsComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty)
      ((inSharpMap U_mem_nonempty).comp a) :=
    comp_isComputable ha (inSharp_isComputable U_mem_nonempty UComputablePresentation)
  have hInner : IsComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      (dsharpPresentation UComputablePresentation U_mem_nonempty) (aSharpInner a) :=
    gMap_isComputable U_mem_nonempty UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) hu
      (pairSharp_isComputable U_mem_nonempty UComputablePresentation)
  exact comp_isComputable (comp_isComputable jSharp_isComputableMap hInner) iSharp_isComputableMap

end DomainTheory.NeighbourhoodSystems
