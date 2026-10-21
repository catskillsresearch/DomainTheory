/-ai
A language lies in S if and only if it is the nonempty denotation of some expression.

If the language lies in S, completeness supplies an expression denoting it and membership supplies nonemptiness. Conversely, soundness sends a nonempty denotation back into S.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.InS_denote_of_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.InS_exists_denote

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


/-- **Characterization of `S` as the regular events of this fragment.** A language `X` is in `S`
exactly when it is the *non-empty* denotation of some `Σ`/`{σ}`/`·`/`∩` expression. This is the
precise content of Scott's "the sets in `S` are each regular events". -/
theorem inS_iff_exists_denote {X : Set (List Bool)} :
    InS X ↔ ∃ e : SExpr, denote e = X ∧ X.Nonempty := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, he, h.nonempty⟩
  · rintro ⟨e, rfl, hne⟩
    exact InS_denote_of_nonempty hne

end Exercise722
end DomainTheory.NeighbourhoodSystems
