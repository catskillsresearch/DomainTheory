/-ai
A word lies in a concatenation of two languages if and only if some cut at most its length puts the prefix in the first language and the suffix in the second.

From a concatenation witness, the cut is the length of the first factor, and taking and dropping that length recover the two factors. Conversely, the prefix and the suffix at the given cut concatenate back to the word.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- A word `w` lies in a concatenation `X·Y` iff it splits as `w = w.take i ++ w.drop i` with the
prefix in `X` and the suffix in `Y` for some cut point `i ≤ |w|`. (The cut point is the length of
the `X`-part.) -/
theorem mem_concat_iff_split {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ i, i ≤ w.length ∧ w.take i ∈ X ∧ w.drop i ∈ Y := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a.length, by simp, ?_, ?_⟩
    · rw [List.take_left]; exact ha
    · rw [List.drop_left]; exact hb
  · rintro ⟨i, _, hpre, hsuf⟩
    exact ⟨w.take i, hpre, w.drop i, hsuf, w.take_append_drop i⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
