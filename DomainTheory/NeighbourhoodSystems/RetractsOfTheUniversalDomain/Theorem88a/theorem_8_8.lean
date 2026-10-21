/-ai
Scott's Theorem 8.8: for every countable neighbourhood system D, the universal system U satisfies D ⊴ U.

The auxiliary form supplies a neighbourhood system D' of subsets of the rationals, an isomorphism from D to D', and a subsystem embedding of D' into U. The relation D ⊴ U is that data.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}









/-- **First sentence of Theorem 8.8 (Scott 1981, PRG-19).** Scott's wording:
"The system `𝒰` is universal in the sense that, for every countable neighbourhood
system `𝒟`, we have `𝒟 ⊴ 𝒰`." This packages `theorem_8_8_a` as that relation. -/
theorem theorem_8_8.{u} {α : Type u} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] : D ⊴ U := by
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩

end DomainTheory.NeighbourhoodSystems
