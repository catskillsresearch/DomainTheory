/-ai
The equation defining the test one from emptiness, zero, and the conditional holds on every total element of the sequence domain.

On the empty string the emptiness test returns true, so the conditional selects false, which is the value of the test one. On a false-headed string the emptiness test returns false and the zero test returns true, so the inner conditional selects false. On a true-headed string both tests return false, so the inner conditional selects true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44


variable {β : Type*}


/-- **Exercise 4.19 (Scott 1981, PRG-19).** `one` is definable from `empty`, `zero`, `cond`: the
equation `one(x) = cond(empty(x), false, cond(zero(x), false, true))` holds on every total element
`σ`. -/
theorem one_def_strElem (σ : Str) : oneMap.toElementMap (strElem σ) = oneDef (strElem σ) := by
  cases σ with
  | nil =>
    -- empty(Λ)=true ⟹ cond picks `false`
    rw [oneDef, emptyMap_strElem, headValC_nil, Exercise326.cond_true,
      oneMap_strElem, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      -- empty=false ⟹ inner cond; zero(0σ)=true ⟹ inner cond picks `false`
      rw [oneDef, emptyMap_strElem, headValC_false, Exercise326.cond_false,
        zeroMap_strElem, headValC_false, Exercise326.cond_true, oneMap_strElem, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strElem, headValC_true, Exercise326.cond_false,
        zeroMap_strElem, headValC_true, Exercise326.cond_false, oneMap_strElem, headValC_true]

end DomainTheory.NeighbourhoodSystems.Exercise419
