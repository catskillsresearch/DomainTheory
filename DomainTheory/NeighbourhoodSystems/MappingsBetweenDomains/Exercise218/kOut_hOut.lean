/-ai
The inverse output of the doubling of a finite string is the string itself.

The proof is by induction on the string. The empty string is immediate. For a cons, the cons equations of doubling and of the inverse output reduce the claim to the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap









/-- **`k` inverts `h` on prefixes.** `kOut (hOut σ) = σ`. -/
theorem kOut_hOut (σ : Str) : kOut (hOut σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b t ih => simp only [hOut_cons, kOut_cons, ih]

end DomainTheory.NeighbourhoodSystems.Exercise218
