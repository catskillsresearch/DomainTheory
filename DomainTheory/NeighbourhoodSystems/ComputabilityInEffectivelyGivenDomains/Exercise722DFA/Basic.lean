module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.sigmaDFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.singleDFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.sigmaDFA_accepts
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.SingleState

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability


/-- The complement DFA recognises the set-complement of the original language (over all of `Σ*`).
(Choice-free; avoids mathlib's classical `accepts_compl`.) -/
theorem complDFA_accepts {σ : Type} (M : DFA Bool σ) (a : SExpr) (h : M.accepts = denote a) :
    (Mᶜ).accepts = (denote a)ᶜ := by
  rw [← h]
  ext w
  exact Iff.rfl

example : Fintype (Unit) := inferInstance
example : DecidableEq (Unit) := inferInstance
example (σ : List Bool) : Fintype (SingleState σ) := by unfold SingleState; infer_instance
example (σ : List Bool) : DecidableEq (SingleState σ) := by unfold SingleState; infer_instance
example {σ₁ σ₂ : Type} [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ × σ₂) := inferInstance
example {σ₁ σ₂ : Type} [DecidableEq σ₁] [DecidableEq σ₂] : DecidableEq (σ₁ × σ₂) := inferInstance
end Exercise722
end DomainTheory.NeighbourhoodSystems
