module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **No `B`-cone reaches "past" a completion.** `encC σ` is never a prefix of `enc τ`: a
"completed" position of `C` never contains, as a subset, a "still going" cone. -/
theorem not_encC_prefix_enc {σ τ : Str} : ¬ encC σ <+: enc τ := by
  induction σ generalizing τ with
  | nil =>
    cases τ with
    | nil => simp [encC_nil]
    | cons c τ' =>
      rw [encC_nil, enc_cons]
      intro h
      obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
      obtain ⟨h3, -⟩ := List.cons_prefix_cons.mp h2
      exact absurd h3 (by decide)
  | cons b σ' ih =>
    cases τ with
    | nil =>
      rw [encC_cons, enc_nil]
      intro h
      exact absurd h.length_le (by simp)
    | cons c τ' =>
      rw [encC_cons, enc_cons]
      intro h
      obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
      obtain ⟨-, h3⟩ := List.cons_prefix_cons.mp h2
      exact ih h3

end Exercise822

end DomainTheory.NeighbourhoodSystems
