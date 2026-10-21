/-ai
The doubled output of a finite string is a prefix of the doubled output of any extension of that string.

The proof is by induction on the prefix. The empty prefix is immediate after simplification. For a cons, the cons equation for doubling extends the inductive prefix witness by the same two bits.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `hOut` grows under extension: `hOut σ <+: hOut (σ ++ t)`. -/
theorem hOut_append (σ t : Str) : hOut σ <+: hOut (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons b s ih =>
    simp only [List.cons_append, hOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, List.cons_append, hu]⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
