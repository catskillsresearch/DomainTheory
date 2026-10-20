module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722
















/-- **Definition 7.1(i), syntactically**, is *exactly language equivalence on `SExpr`*:
`Xₙ ∩ Xₘ = X_k ↔ denote (cap eₙ eₘ) = denote e_k`. -/
theorem interEq_iff (a b k : SExpr) :
    denote a ∩ denote b = denote k ↔ denote (.cap a b) = denote k := by
  rw [denote_cap]

end Exercise722
end DomainTheory.NeighbourhoodSystems
