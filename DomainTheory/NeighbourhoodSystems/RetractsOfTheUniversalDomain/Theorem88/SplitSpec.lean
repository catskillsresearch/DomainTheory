/-ai
A splitting operation satisfies the specification when, whenever emptiness of a set A matches emptiness of a set B of rationals and B is empty or a neighbourhood of U, both outputs on the next set are empty or neighbourhoods of U, emptiness of the first output matches emptiness of A met with that set, emptiness of the second output matches emptiness of the difference, the two outputs are disjoint, and their union is B.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- **The abstract specification a splitting operation must satisfy** — exactly `exists_split`'s
conclusion, as a `Prop` about a *total* function `split`. Both the classical `splitChoice` (via
`Classical.choice`) and the effective, computable `splitEff` (Theorem 8.8(b)) satisfy this. -/
def SplitSpec (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ) : Prop :=
  ∀ {A : Set α} {B : Set ℚ}, (A = ∅ ↔ B = ∅) → (B = ∅ ∨ U.mem B) → ∀ Xn : Set α,
    ((split A B Xn).1 = ∅ ∨ U.mem (split A B Xn).1) ∧
      ((split A B Xn).2 = ∅ ∨ U.mem (split A B Xn).2) ∧
      (A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅) ∧
      (A \ Xn = ∅ ↔ (split A B Xn).2 = ∅) ∧
      (split A B Xn).1 ∪ (split A B Xn).2 = B ∧
      (split A B Xn).1 ∩ (split A B Xn).2 = ∅

end DomainTheory.NeighbourhoodSystems
