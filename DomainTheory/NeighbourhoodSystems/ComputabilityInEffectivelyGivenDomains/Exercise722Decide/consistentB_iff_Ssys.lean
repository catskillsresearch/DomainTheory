/-ai
If the languages of a and of b both lie in S, then consistentB a b is true if and only if the intersection of those languages lies in S.

Rewrite by the denotation of an intersection expression and by the Boolean criterion for consistentB, then reverse the positivity equivalence of S applied to the two membership hypotheses.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_isPositive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}














variable {σ : Type}














/-- **Definition 7.1 (ii) for encoded neighbourhoods:** when `denote a`, `denote b ∈ S`,
`consistentB` agrees with membership of the intersection in `S`. -/
theorem consistentB_iff_Ssys (a b : SExpr) (ha : InS (denote a)) (hb : InS (denote b)) :
    consistentB a b = true ↔ InS (denote a ∩ denote b) := by
  rw [← denote_cap, consistentB_iff]
  exact Iff.symm (Ssys_isPositive (Ssys_mem.mpr ha) (Ssys_mem.mpr hb))

end Exercise722
end DomainTheory.NeighbourhoodSystems
