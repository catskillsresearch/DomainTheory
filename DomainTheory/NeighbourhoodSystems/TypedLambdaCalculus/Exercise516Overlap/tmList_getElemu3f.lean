/-ai
For j strictly below n, the j-th entry of the length-n Thue–Morse prefix is the bit at j.

Unfold the prefix as the map of the bit function along the range, read the entry of the range, and the resulting equation holds by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems


open Example44 ExampleB NeighborhoodSystem

/-- The `j`-th bit of the length-`n` Thue–Morse prefix is `tm j`. -/
theorem tmList_getElem? {n j : ℕ} (h : j < n) : (tmList n)[j]? = some (tm j) := by
  rw [tmList, List.getElem?_map, List.getElem?_range h]
  rfl

end DomainTheory.NeighbourhoodSystems.Exercise516
