module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterElem_succ_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_prefix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_iterate_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterElem_le_fixElement

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
















/-- **Property (a), prefix form.** Every Thue–Morse parity prefix is a prefix of `t`:
`(tmList n)⊥ ⊑ t` for all `n`. -/
theorem tmList_le_tElt (n : ℕ) : strBot (tmList n) ≤ tElt := by
  have hpre : tmList n <+: expand^[n] [false] := by
    rw [expand_iterate_eq]; exact tmList_prefix (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc strBot (tmList n) ≤ strBot (expand^[n] [false]) :=
        strBot_le_strBot_iff.mpr hpre
    _ = tmOp.iterElem (n + 1) := (iterElem_succ_eq n).symm
    _ ≤ tElt := iterElem_le_fixElement tmOp (n + 1)

end DomainTheory.NeighbourhoodSystems.Exercise516
