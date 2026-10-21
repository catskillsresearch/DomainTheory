/-ai
The uncurried pairing function is injective.

From equal pairing values the diagonal sums agree. If one sum were strictly smaller, the pairing value on that diagonal would lie strictly below the next triangular number, that triangular number would be at most the triangular number of the larger sum, and that triangular number would be at most the other pairing value, which is absurd, and the symmetric case is the same. With the sums equal, cancelling the common triangular number makes the second coordinates agree, and then the first coordinates agree. Substituting these equalities identifies the pairs.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
import all Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_lt_tri_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- **The function is one-one.** The diagonal `s = n+m` is recovered as the unique `s` with
`T(s) ≤ num n m < T(s+1)`; then `m` is the offset and `n = s - m`. -/
theorem num_injective : Function.Injective numP := by
  rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ h
  have h' : num n₁ m₁ = num n₂ m₂ := h
  have hs : n₁ + m₁ = n₂ + m₂ := by
    rcases lt_trichotomy (n₁ + m₁) (n₂ + m₂) with hlt | heq | hgt
    · exfalso
      have h1 : num n₁ m₁ < tri (n₁ + m₁ + 1) := num_lt_tri_succ n₁ m₁
      have h2 : tri (n₁ + m₁ + 1) ≤ tri (n₂ + m₂) := tri_mono (by omega)
      have h3 : tri (n₂ + m₂) ≤ num n₂ m₂ := by unfold num; omega
      omega
    · exact heq
    · exfalso
      have h1 : num n₂ m₂ < tri (n₂ + m₂ + 1) := num_lt_tri_succ n₂ m₂
      have h2 : tri (n₂ + m₂ + 1) ≤ tri (n₁ + m₁) := tri_mono (by omega)
      have h3 : tri (n₁ + m₁) ≤ num n₁ m₁ := by unfold num; omega
      omega
  have hbase : tri (n₁ + m₁) + m₁ = tri (n₂ + m₂) + m₂ := h'
  rw [hs] at hbase
  have hm : m₁ = m₂ := by omega
  have hn : n₁ = n₂ := by omega
  subst hm; subst hn; rfl

end DomainTheory.NeighbourhoodSystems.Exercise513
