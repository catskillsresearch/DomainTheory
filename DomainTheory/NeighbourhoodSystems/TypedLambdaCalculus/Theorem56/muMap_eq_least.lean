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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec_found
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muMap_natElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec_climb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)


section Mu

variable (f : ApproximableMap (prod N N) N)


/-- **Capstone (μ-scheme correctness).** If `n₀` is the *least* zero of `f(·, m̂)` — that is,
`f(n̂₀, m̂) = 0̂` and `f(î, m̂)` is a positive total for every `i < n₀` — then `μ(m̂) = n̂₀`. -/
theorem muMap_eq_least {m n₀ : ℕ}
    (hzero : f.toElementMap (pair (natElem n₀) (natElem m)) = natElem 0)
    (hpos : ∀ i < n₀, ∃ j, f.toElementMap (pair (natElem i) (natElem m)) = natElem (j + 1)) :
    (muMap f).toElementMap (natElem m) = natElem n₀ := by
  rw [muMap_natElem]
  have hclimb := muRec_climb f m n₀ 0 (by simpa using hpos)
  rw [show (zeroElt : N.Element) = natElem 0 from rfl, hclimb, Nat.zero_add]
  exact muRec_found f hzero

end Mu
end DomainTheory.NeighbourhoodSystems.Theorem56
