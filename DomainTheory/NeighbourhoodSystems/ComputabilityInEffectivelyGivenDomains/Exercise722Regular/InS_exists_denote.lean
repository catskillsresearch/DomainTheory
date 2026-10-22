/-ai
Every member of S is the denotation of some expression.

Induction on membership in S sends the universal language to the universal expression and a singleton language to the singleton expression. A concatenation is the concatenation of the expressions given by the inductive hypotheses, and an intersection is the intersection of those expressions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


/-- **Completeness.** Every member of `S` is the denotation of some `S`-term. -/
theorem InS_exists_denote {X : Set (List Bool)} (h : InS X) : ∃ e : SExpr, denote e = X := by
  induction h with
  | univ => exact ⟨.sigma, rfl⟩
  | singleton σ => exact ⟨.single σ, rfl⟩
  | mul _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cat ea eb, rfl⟩
  | inter _ _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cap ea eb, rfl⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
