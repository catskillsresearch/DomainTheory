/-ai
On a left state and a letter, the concatenation automaton steps to the left copy of the first automaton's step. On a left state and an epsilon it steps to those right copies of the second automaton's start states for which the left state is accepting. On a right state and a letter it steps to the right copy of the second automaton's step, and on a right state and an epsilon it steps to nothing. Its start states are the left copies of the first automaton's start states, and its accept states are the right copies of the second automaton's accept states.

Each of these identities is the corresponding clause of the definition.

The sum of two finite state types is finite.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.EpsilonNFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.catEps

@[expose] public section

/-!
# Exercise 7.22 — the concatenation automaton (the crux mathlib lacks)

mathlib provides NFA/εNFA/DFA with intersection (`DFA.inter`) and complement, but **no
language-concatenation automaton**. This file builds one and proves it correct, choice-free.

Given two NFAs `M₁`, `M₂` we form an `εNFA` `catEps M₁ M₂` on the sum state type `σ₁ ⊕ σ₂`:
copies of `M₁` (on the `inl` side) and `M₂` (on the `inr` side), with an **ε-edge from every
accept state of `M₁` to every start state of `M₂`**. The headline result is

  `(catEps M₁ M₂).accepts = M₁.accepts * M₂.accepts`   (`catEps_accepts`)

proved via the closed form (`catEps_eval`)

  `(catEps M₁ M₂).eval x = inl '' (M₁.eval x) ∪ inr '' { t | ∃ u v, x = u ++ v ∧ u ∈ M₁.accepts ∧
                                                                  t ∈ M₂.eval v }`

i.e. the reachable `inr`-states after reading `x` are exactly the `M₂`-states reachable from some
split `x = u ++ v` with the `M₁`-prefix `u` accepted. The `Sum` state type stays `Fintype`, so this
plugs into the `Fintype`-DFA/NFA decision route (`Exercise722DFA.lean`).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}


variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

@[simp] theorem catEps_step_inl_some (s : σ₁) (c : Bool) :
    (catEps M₁ M₂).step (inl s) (some c) = inl '' M₁.step s c := rfl
@[simp] theorem catEps_step_inl_none (s : σ₁) :
    (catEps M₁ M₂).step (inl s) none = {t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start} := rfl
@[simp] theorem catEps_step_inr_some (s : σ₂) (c : Bool) :
    (catEps M₁ M₂).step (inr s) (some c) = inr '' M₂.step s c := rfl
@[simp] theorem catEps_step_inr_none (s : σ₂) :
    (catEps M₁ M₂).step (inr s) none = ∅ := rfl
@[simp] theorem catEps_start : (catEps M₁ M₂).start = inl '' M₁.start := rfl
@[simp] theorem catEps_accept : (catEps M₁ M₂).accept = inr '' M₂.accept := rfl

example [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ ⊕ σ₂) := inferInstance
end Exercise722
end DomainTheory.NeighbourhoodSystems
