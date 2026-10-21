/-ai
If n₀ is the least zero of f at the numeral m, in the sense that f at the numerals n₀ and m is the numeral 0 and f at each smaller numeral and m is a positive numeral, then the minimization at the numeral m is the numeral n₀.

Rewrite the minimization at the numeral m as the search at zero and m. Climbing from 0 across those positive values reaches n₀, using that the zero element is the numeral 0 and that adding zero on the left leaves n₀ unchanged. The found lemma then returns the numeral n₀.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.Basic
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
