/-ai
The doubled encoding of one string is a prefix of the doubled encoding of another if and only if the first string is a prefix of the second.

One direction is the preservation of prefixes by doubling. For the other, induct on the first string. The empty string is a prefix of every string. If the first string is nonempty and the second is empty, extracting a continuation from the prefix is impossible by simplification. If both are nonempty, two prefix steps give a common first bit and the inductive hypothesis applies to the tails.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_prefix_of_prefix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **`enc` is prefix-reflecting.** Doubling never merges or confuses distinct prefixes: a prefix
relation between doubled strings comes from a prefix relation between the originals. -/
theorem enc_prefix_iff {σ τ : Str} : enc σ <+: enc τ ↔ σ <+: τ := by
  refine ⟨?_, enc_prefix_of_prefix⟩
  induction σ generalizing τ with
  | nil => intro _; exact List.nil_prefix
  | cons b σ' ih =>
    cases τ with
    | nil =>
      intro h
      rw [enc_cons, enc_nil] at h
      obtain ⟨t, ht⟩ := h
      simp at ht
    | cons c τ' =>
      intro h
      rw [enc_cons, enc_cons, List.cons_prefix_cons, List.cons_prefix_cons] at h
      obtain ⟨rfl, -, h3⟩ := h
      rw [List.cons_prefix_cons]
      exact ⟨rfl, ih h3⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
