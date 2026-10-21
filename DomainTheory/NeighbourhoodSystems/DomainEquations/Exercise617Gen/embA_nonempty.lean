/-ai
If a set of finite strings is nonempty, then its letter-prefixed copy is nonempty.

A string of the set yields the string formed by writing the letter in front of it, and that longer string belongs to the prefixed copy.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]


section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]


theorem embA_nonempty {a : A} {X : Set (Strn A)} (hX : X.Nonempty) : (embA a X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨a :: w', w', rfl, hw'⟩

end Iso
end DomainTheory.NeighbourhoodSystems.Exercise617Gen
