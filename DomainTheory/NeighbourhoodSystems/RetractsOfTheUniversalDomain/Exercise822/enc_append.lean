/-ai
The doubling encoding distributes over concatenation.

Induct on the first string. The empty case simplifies. In the cons case, simplification uses the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

theorem enc_append (σ τ : Str) : enc (σ ++ τ) = enc σ ++ enc τ := by
  induction σ with
  | nil => simp
  | cons b σ' ih => simp [ih]

end Exercise822

end DomainTheory.NeighbourhoodSystems
