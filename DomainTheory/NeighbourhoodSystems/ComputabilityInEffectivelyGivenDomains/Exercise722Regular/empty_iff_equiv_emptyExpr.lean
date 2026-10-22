/-ai
The intersection of the languages of two expressions is empty if and only if that intersection expression denotes the same language as emptyExpr.

Rewrite by the denotation of emptyExpr.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


/-- **Definition 7.1(ii), syntactically.** Inconsistency of `eₙ, eₘ` — emptiness of `Xₙ ∩ Xₘ` — is
exactly *language-equivalence of `cap eₙ eₘ` with `emptyExpr`*. Consistency (relation (ii)) is its
**negation**, so even (ii) is an instance of deciding language equivalence on `SExpr` (here:
equivalence to `∅`). Stated as an emptiness-equivalence to keep it choice-free (recovering a witnessing
element from `≠ ∅` is the one genuinely non-constructive step, and is not needed for the decision). -/
theorem empty_iff_equiv_emptyExpr (a b : SExpr) :
    denote (.cap a b) = (∅ : Set (List Bool)) ↔ denote (.cap a b) = denote emptyExpr := by
  rw [denote_emptyExpr]

end Exercise722
end DomainTheory.NeighbourhoodSystems
