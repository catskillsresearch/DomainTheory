/-ai
The code of the representing closure of a countably algebraic lattice is a closure operation.

A pair from the identity combinator has its second component in a finite set, and expansiveness of the representing closure puts that component into the representing closure of the finite set, so the pair lies in the code. The code equals the graph of its own iterate because applying the code twice is the representing closure applied twice, which equals one application by idempotence.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_idem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem representClosureCode_isClosure
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) :
    IsClosure (representClosureCode D) := by
  constructor
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, representClosure_expansive D (e n) hm⟩
  · change representClosureCode D =
      graph (fun x => funOf (representClosureCode D)
        (funOf (representClosureCode D) x))
    apply graph_ext
    intro x
    rw [representClosureCode_app, representClosureCode_app,
      representClosure_idem]

end DomainTheory.DataTypesAsLattices
