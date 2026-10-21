/-ai
Scott's definability theorem for a Scott-continuous function f of n arguments in Pω: computability of f on finite tuples holds if and only if its curried graph is recursively enumerable, that graph is recursively enumerable if and only if it is combinatory, and the graph is lambda-definable if and only if it is combinatory.

A computable finite-arity map contributes the recursive enumerability of its curried graph, and recursive enumerability together with the continuity hypothesis hf restores computability. The second equivalence is IsRE.iff_combinatory. A lambda definition by a term t is combinatory by theorem_2_4_closed after rewriting by the defining equation, and a combinatory element is lambda-definable by combinatory_isLambdaDefinable.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.combinatory_isLambdaDefinable
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eiff_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4








































/-- **Scott 1976, Theorem 2.6 (The definability theorem).**
For a `k`-ary continuous `f`, computability of the finite-argument relation,
recursive enumerability of the nested graph, combinatory definability, and
closed LAMBDA-definability agree. -/
theorem theorem_2_6_fin {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) :
    (IsComputableFin f ↔ IsRE (curryFin f)) ∧
      (IsRE (curryFin f) ↔ IsCombinatory (curryFin f)) ∧
      (IsLambdaDefinable (curryFin f) ↔ IsCombinatory (curryFin f)) := by
  refine ⟨?_, IsRE.iff_combinatory, ?_⟩
  · exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
  · exact ⟨fun ⟨t, ht⟩ => by simpa [ht] using theorem_2_4_closed t,
      combinatory_isLambdaDefinable⟩

end DomainTheory.DataTypesAsLattices
