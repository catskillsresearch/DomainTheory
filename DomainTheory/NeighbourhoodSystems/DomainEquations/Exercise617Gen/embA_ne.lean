/-ai
If two letters are distinct and a set of finite strings is nonempty, its copy prefixed by the first letter differs from the copy of any set prefixed by the second letter.

A string of the nonempty set gives a string in the first prefixed copy, hence, by the assumed equality, in the second. That membership forces the two letters to be equal, contradicting the hypothesis that they differ.
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


theorem embA_ne {a a' : A} (h : a ≠ a') {X Y : Set (Strn A)} (hX : X.Nonempty) :
    embA a X ≠ embA a' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (a :: w') ∈ embA a' Y := heq ▸ (⟨w', rfl, hw'⟩ : (a :: w') ∈ embA a X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he; exact h he.1

end Iso
end DomainTheory.NeighbourhoodSystems.Exercise617Gen
