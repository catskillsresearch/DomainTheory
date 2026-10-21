/-ai
Interpreting every entry of a list of natural numbers as a boolean succeeds if and only if every entry is 0 or 1.

Induction on the list. The empty list succeeds. For a head and a tail, success forces the head to interpret as a boolean, hence to be 0 or 1, and the tail satisfies the inductive claim. Conversely, the hypothesis makes the head interpretation and the tail map succeed, so a failed head or tail contradicts it and the successful case simplifies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool_isSome_iff
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBinDigit_of_natBool_some

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem mapM_natBool_isSome_iff (l : List ℕ) :
    (l.mapM natBool).isSome = true ↔ ∀ x ∈ l, x = 0 ∨ x = 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapM_cons]
    constructor
    · intro h
      cases hnx : natBool x with
      | none => simp [hnx] at h
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [hnx, htx] at h
        | some ts =>
          have hxs' : (xs.mapM natBool).isSome = true := by simp [htx]
          intro y hy
          rcases List.mem_cons.mp hy with hEq | hyTail
          · rw [hEq]
            exact natBinDigit_of_natBool_some x hnx
          · exact ih.mp hxs' y hyTail
    · intro h
      have hx : (natBool x).isSome = true :=
        (natBool_isSome_iff x).2 (h x (List.mem_cons_self ..))
      have hxs : (xs.mapM natBool).isSome = true :=
        ih.mpr fun y hy => h y (List.mem_cons_of_mem x hy)
      cases hnx : natBool x with
      | none =>
        rcases h x (List.mem_cons_self ..) with h0 | h1
        · subst h0; simp [natBool] at hnx
        · subst h1; simp [natBool] at hnx
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [htx] at hxs
        | some ts => simp

end Exercise722

end DomainTheory.NeighbourhoodSystems
