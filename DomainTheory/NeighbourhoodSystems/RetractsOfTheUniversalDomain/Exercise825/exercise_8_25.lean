/-ai
The domain obtained as the fixed neighbourhood of the fixed point of the continuous operator of the combinator is isomorphic to its own function space.

The proof is the main theorem of the fixed-point construction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

/-- **Exercise 8.25 (Scott 1981, PRG-19), the answer.** The concrete domain
`D := fixedNbhd (fixOp (tOpMap cCombinator))` (built in `Exercise825FixedPoint.lean` by the
fixed-point method of Exercise 8.23, applied to `T(a) := a → 𝒰^∞`) satisfies `D ≅ D → D`. -/
theorem exercise_8_25 :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  exercise_8_25_main

end DomainTheory.NeighbourhoodSystems
