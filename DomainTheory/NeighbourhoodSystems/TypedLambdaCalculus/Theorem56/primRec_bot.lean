/-ai
Primitive recursion at bottom and the numeral m is bottom.

Unfold the defining recursion and use that the zero test of bottom is the bottom of the truth domain, that this equals Example23.botElt, and that the conditional on that bottom is bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.T_bot_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primRec_rec

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_bot
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)


section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


/-- **Primitive recursion is strict in the recursion argument.** `h̄(⊥, m̂) = ⊥`. -/
theorem primRec_bot (m : ℕ) :
    (primRec f g).toElementMap (pair N.bot (natElem m)) = N.bot := by
  rw [primRec_rec, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end PrimRec
end DomainTheory.NeighbourhoodSystems.Theorem56
