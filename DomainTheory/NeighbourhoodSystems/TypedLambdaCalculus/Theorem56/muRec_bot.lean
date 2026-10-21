/-ai
If f at the numerals n and m is bottom, the binary search at that pair is bottom.

Unfold the defining recursion, substitute the hypothesis, and use that the zero test of bottom is the bottom of the truth domain, that this equals Example23.botElt, and that the conditional on that bottom is bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.T_bot_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec_rec

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_bot
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)


section Mu

variable (f : ApproximableMap (prod N N) N)


/-- **μ is strict in the test.** If `f(n̂, m̂) = ⊥`, the search diverges. -/
theorem muRec_bot {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = N.bot) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = N.bot := by
  rw [muRec_rec, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end Mu
end DomainTheory.NeighbourhoodSystems.Theorem56
