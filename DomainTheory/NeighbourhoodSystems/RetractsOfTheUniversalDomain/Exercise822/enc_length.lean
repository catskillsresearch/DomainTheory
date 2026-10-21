/-ai
The length of the doubled encoding of a string is twice the length of the string.

Induct on the string. The empty case simplifies. In the cons case, simplification uses the inductive hypothesis and the arithmetic is the ring law.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

theorem enc_length (σ : Str) : (enc σ).length = 2 * σ.length := by
  induction σ with
  | nil => simp
  | cons b σ' ih => simp [ih]; ring

end Exercise822

end DomainTheory.NeighbourhoodSystems
