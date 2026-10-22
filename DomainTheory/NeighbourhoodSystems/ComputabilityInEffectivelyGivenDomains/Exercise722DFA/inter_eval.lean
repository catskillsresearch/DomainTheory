module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability


/-- The product DFA evaluates componentwise. (Choice-free; avoids mathlib's classical
`accepts_inter`.) -/
theorem inter_eval {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂) (w : List Bool) :
    (M₁.inter M₂).eval w = (M₁.eval w, M₂.eval w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton, DFA.eval_append_singleton, DFA.eval_append_singleton, ih]
    rfl

end Exercise722
end DomainTheory.NeighbourhoodSystems
