module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraicu2ecompact_finite_support
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def representClosureCode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) : Pomega :=
  graph (representClosure D)

namespace representClosureCode

theorem app {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    funOf (representClosureCode D) x = representClosure D x :=
  beta (representClosure.isScottContinuous D) x

theorem isClosure
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) :
    Closure (representClosureCode D) := by
  constructor
  constructor
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, representClosure.expansive D (e n) hm⟩
  · constructor
    change representClosureCode D =
      graph (fun x => funOf (representClosureCode D)
        (funOf (representClosureCode D) x))
    apply graph_ext
    intro x
    rw [representClosureCode.app, representClosureCode.app,
      representClosure.idem]

end representClosureCode

end DomainTheory.DataTypesAsLattices
