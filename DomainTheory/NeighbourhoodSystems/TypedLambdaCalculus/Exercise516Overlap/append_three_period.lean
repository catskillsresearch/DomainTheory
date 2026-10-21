/-ai
In the concatenation of three copies of a list a, an index m strictly below twice the length of a carries the same entry as the index shifted by the length of a.

If m lies below the length, the left side reads the first copy and the shifted index reads the second copy at the same place. If m is at least the length, the left side reads the second copy and the shifted index reads the third copy at the same place.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems






open Example44 ExampleB NeighborhoodSystem

/-- Positions differing by `|a|` inside `a ++ (a ++ a)` carry the same symbol, for indices `< 2|a|`
(the three copies of `a` are identical). -/
theorem append_three_period {α : Type*} (a : List α) (m : ℕ) (hm : m < 2 * a.length) :
    (a ++ (a ++ a))[m]? = (a ++ (a ++ a))[m + a.length]? := by
  rcases lt_or_ge m a.length with h | h
  · rw [List.getElem?_append_left h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega, List.getElem?_append_left h]
  · rw [List.getElem?_append_right h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega,
      List.getElem?_append_left (by omega : m - a.length < a.length),
      List.getElem?_append_right (by omega : a.length ≤ m)]

end DomainTheory.NeighbourhoodSystems.Exercise516
