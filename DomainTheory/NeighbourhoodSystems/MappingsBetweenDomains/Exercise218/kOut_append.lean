/-ai
The inverse output of a finite string is a prefix of the inverse output of any extension of that string.

The proof follows the recursion of the inverse output. The empty string and a singleton simplify immediately. For a string that starts with two bits, the cons equation extends the inductive prefix witness by the kept first bit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_cons
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_single
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `kOut` grows under extension: `kOut σ <+: kOut (σ ++ t)`. -/
theorem kOut_append (σ t : Str) : kOut σ <+: kOut (σ ++ t) := by
  induction σ using kOut.induct with
  | case1 => simp
  | case2 _ => simp
  | case3 b c t' ih =>
    simp only [List.cons_append, kOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, hu]⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
