module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- Reindexing a non-dependent `ι → E` arrow type along a bijection of index types is an order
isomorphism, for the pointwise order on both sides. (Named distinctly from `Exercise324Iter.lean`'s
`piCongrOrderIso`, which reindexes *dependent* `Pi` types along a fixed index type instead.) -/
def arrowReindexOrderIso {ι ι' : Type*} (e : ι ≃ ι') (E : Type*) [Preorder E] :
    (ι → E) ≃o (ι' → E) where
  toFun f i' := f (e.symm i')
  invFun g i := g (e i)
  left_inv f := by funext i; simp
  right_inv g := by funext i'; simp
  map_rel_iff' := by
    intro f g
    constructor
    · intro h i
      simpa using h (e i)
    · intro h i'
      simpa using h (e.symm i')

end DomainTheory.NeighbourhoodSystems
