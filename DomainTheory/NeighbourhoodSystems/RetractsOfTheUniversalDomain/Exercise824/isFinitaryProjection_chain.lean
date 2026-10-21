/-ai
If two approximable maps from the pair space into the function space send pairs of finitary projections to finitary projections, then every approximant pair consists of finitary projections.

The proof is by induction on the index. At zero, the two approximants rewrite as constant maps at the bottom, and each constant map at the bottom is a finitary projection. At a successor, the approximants rewrite as the two maps applied to the preceding pair, and the hypothesis applies to the inductive pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aOp_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bOp_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aOp_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bOp_zero

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}


/-- Every approximant pair `(aOp s t n, bOp s t n)` consists of finitary projections, provided
`s`/`t` send pairs of finitary projections to finitary projections. -/
theorem isFinitaryProjection_chain (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b)) :
    ∀ n, IsFinitaryProjection (aOp s t n) ∧ IsFinitaryProjection (bOp s t n) := by
  intro n
  induction n with
  | zero =>
    rw [aOp_zero, bOp_zero]
    exact ⟨Exercise823.isFinitaryProjection_constMap_bot E,
      Exercise823.isFinitaryProjection_constMap_bot E⟩
  | succ k ih =>
    rw [aOp_succ, bOp_succ]
    exact hst _ _ ih.1 ih.2

end Exercise824
end DomainTheory.NeighbourhoodSystems
