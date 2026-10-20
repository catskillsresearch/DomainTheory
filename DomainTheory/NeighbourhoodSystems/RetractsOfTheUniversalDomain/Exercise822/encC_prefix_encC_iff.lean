module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_length

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **Two completions relate only to themselves.** `encC σ <+: encC τ ↔ σ = τ`: distinct completed
positions of `C` become disjoint (never nested) `B`-cones. -/
theorem encC_prefix_encC_iff {σ τ : Str} : encC σ <+: encC τ ↔ σ = τ := by
  constructor
  · induction σ generalizing τ with
    | nil =>
      intro h
      cases τ with
      | nil => rfl
      | cons c τ' =>
        exfalso
        rw [encC_nil, encC_cons] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨h3, -⟩ := List.cons_prefix_cons.mp h2
        exact absurd h3 (by decide)
    | cons b σ' ih =>
      intro h
      cases τ with
      | nil =>
        exfalso
        rw [encC_cons, encC_nil] at h
        have hlen := h.length_le
        simp only [List.length_cons, List.length_nil, encC_length] at hlen
        omega
      | cons c τ' =>
        rw [encC_cons, encC_cons] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨-, h3⟩ := List.cons_prefix_cons.mp h2
        rw [ih h3]
  · rintro rfl; exact List.prefix_rfl

end Exercise822

end DomainTheory.NeighbourhoodSystems
