module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.strictId
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.strictProj₀
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.qSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.kSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argY
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primRec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.T_bot_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.strictProju2080_apply

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_bot
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)


/-- Strict in the second argument: `proj₀(n̂, ⊥) = ⊥`. -/
theorem strictProj₀_bot_right (n : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) N.bot) = N.bot := by
  rw [strictProj₀_apply, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end DomainTheory.NeighbourhoodSystems.Theorem56
