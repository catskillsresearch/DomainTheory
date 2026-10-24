module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_24
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9

public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Data.Set.Defs

@[expose] public section

section
universe u
namespace DomainTheory.NeighbourhoodSystems
/- concordance: source L2143 DEFINITION 4.5 Peano axioms -/
/-- **Definition 4.5 (Scott 1981, PRG-19).** A *model for Peano's Axioms*: a type `N` with a
distinguished element `zero` and a unary `succ`essor, satisfying

* (i)   `zero ≠ succ n` for all `n`                       (`zero_ne_succ`);
* (ii)  `succ` is injective (`n⁺ = m⁺ ⟹ n = m`)          (`succ_injective`);
* (iii) **mathematical induction**: any `s ⊆ N` with `zero ∈ s` and closed under `succ`
        (`∀ n ∈ s, succ n ∈ s`, i.e. Scott's `x⁺ ⊆ x`) is all of `N`
        (`∀ n, n ∈ s`, i.e. Scott's `x = N`)              (`induction`). -/
structure PeanoModel (N : Type u) where
  /-- The distinguished zero `0 ∈ N`. -/
  zero : N
  /-- The unary successor `⁺ : N → N`. -/
  succ : N → N
  /-- **4.5(i)** `0 ≠ n⁺`. -/
  zero_ne_succ : ∀ n, zero ≠ succ n
  /-- **4.5(ii)** the successor is one-one. -/
  succ_injective : Function.Injective succ
  /-- **4.5(iii)** the induction principle (point form of `x⁺ ⊆ x ⟹ x = N`). -/
  induction : ∀ (s : Set N), zero ∈ s → (∀ n ∈ s, succ n ∈ s) → ∀ n, n ∈ s

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}

/-- Scott's least fixed point `r ⊆ N × M`, realized as the inductively generated relation: the
least relation containing `(0, □)` and closed under `(n, m) ↦ (n⁺, m#)`. The two constructors are
Scott's facts (i) `0 r □` and (ii) `n r m ⟹ n⁺ r m#`. By Theorem 4.1 this *is* the least fixed
point of the approximable operator `u ↦ {(0,□)} ∪ {(n⁺,m#) ∣ (n,m) ∈ u}` on `P(N × M)`. -/
inductive Graph (P : PeanoModel M) (Q : PeanoModel N) : M → N → Prop
  | base : Graph P Q P.zero Q.zero
  | step : ∀ {m n}, Graph P Q m n → Graph P Q (P.succ m) (Q.succ n)

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- The construction is symmetric in the two models: `Graph P Q m n` swaps to `Graph Q P n m`.
(This is why the relation is one-one in *both* directions, as Scott notes: "the rôles of `N` and
`M` are completely symmetric".) -/
theorem Graph.swap {P : PeanoModel M} {Q : PeanoModel N} {m : M} {n : N}
    (h : Graph P Q m n) : Graph Q P n m := by
  induction h with
  | base => exact Graph.base
  | step _ ih => exact Graph.step ih

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- **Inversion at a successor (uses 4.5(i)/(ii)).** Anything related to `n⁺` on the left comes
from a relation `n r n₀` with right value a successor: `n⁺ r k ⟹ ∃ n₀, n r n₀ ∧ k = n₀#`. -/
theorem graph_succ_right (P : PeanoModel M) (Q : PeanoModel N) {m : M} {k : N}
    (h : Graph P Q (P.succ m) k) : ∃ n, Graph P Q m n ∧ k = Q.succ n := by
  generalize hz : P.succ m = z at h
  cases h with
  | base => exact absurd hz.symm (P.zero_ne_succ _)
  | step h' =>
    rename_i m0 n0
    have hm : m = m0 := P.succ_injective hz
    subst hm
    exact ⟨n0, h', rfl⟩

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- **Inversion at `0` (uses 4.5(i)).** Anything related to `0` on the left is `□` on the right:
`0 r k ⟹ k = □`. (The other generating rule would force `0 = n⁺`, impossible by 4.5(i).) -/
theorem graph_zero_right (P : PeanoModel M) (Q : PeanoModel N) {k : N}
    (h : Graph P Q P.zero k) : k = Q.zero := by
  generalize hz : P.zero = z at h
  cases h with
  | base => rfl
  | step _ => exact absurd hz (P.zero_ne_succ _)

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- Each element of the left model is related by `Graph` to exactly one element of the right
model. Proved by the induction principle 4.5(iii) on the set `{m ∣ ∃! n, m r n}`: the base case
is the `0`-inversion `graph_zero_right`, the step case the successor-inversion `graph_succ_right`
together with 4.5(ii). -/
theorem exists_unique_right (P : PeanoModel M) (Q : PeanoModel N) (m : M) :
    ∃! n, Graph P Q m n := by
  refine P.induction {m | ∃! n, Graph P Q m n} ?_ ?_ m
  · exact ⟨Q.zero, Graph.base, fun k hk => graph_zero_right P Q hk⟩
  · rintro m' ⟨n', hn', huniq⟩
    refine ⟨Q.succ n', Graph.step hn', fun k hk => ?_⟩
    obtain ⟨n'', hn'', rfl⟩ := graph_succ_right P Q hk
    rw [huniq n'' hn'']

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- Dually (by `Graph.swap`), each element of the right model is related to exactly one element of
the left model. -/
theorem exists_unique_left (P : PeanoModel M) (Q : PeanoModel N) (n : N) :
    ∃! m, Graph P Q m n := by
  obtain ⟨m, hm, huniq⟩ := exists_unique_right Q P n
  exact ⟨m, hm.swap, fun y hy => huniq y hy.swap⟩

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


end PeanoModel
end
end DomainTheory.NeighbourhoodSystems
end
