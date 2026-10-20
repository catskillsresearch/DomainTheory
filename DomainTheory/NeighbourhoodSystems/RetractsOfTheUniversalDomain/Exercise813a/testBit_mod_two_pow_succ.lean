module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.testBit_mod_two_pow

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- Specialization of `testBit_mod_two_pow` used repeatedly below: reducing mod `2^(i+1)` never
disturbs bit `i` itself. -/
theorem testBit_mod_two_pow_succ (n i : ℕ) :
    (n % 2 ^ (i + 1)).testBit i = n.testBit i := by
  rw [testBit_mod_two_pow]; simp

end DomainTheory.NeighbourhoodSystems
