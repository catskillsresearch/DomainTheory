/-ai
This file gathers and re-exports the infinite iterate of Exercise 3.16, the bijection of a sum of two copies of the natural numbers with the natural numbers, reindexing of function types, the sum-arrow order isomorphism, interleaving of sequences, and the product order isomorphism of an infinite power. The commentary records that interleaving transports along the sequence equivalence of the infinite iterate to an isomorphism of an infinite power with its product, and in particular for the universal domain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.arrowReindexOrderIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.sumArrowOrderIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.interleaveOrderIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.powProdOrderIso

@[expose] public section

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), step 2 — `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`

Scott's hint asks us to first establish `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`, where `𝒰^∞` is the countable power of
the universal domain `𝒰` with itself. We take `𝒰^∞ := iterSys 𝒰` (Exercise 3.16's infinite iterate,
already available with a full API: `iterSeqEquiv`, `iter_isomorphic`, `projN`, effective givenness).

The isomorphism `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞` is the domain-level shadow of the classical fact that a pair of
sequences can be interleaved into a single sequence without loss of information: `ℕ ⊕ ℕ ≃ ℕ`
(`Equiv.natSumNatEquivNat`) reindexes `(ℕ → E) × (ℕ → E) ≅ (ℕ ⊕ ℕ → E) ≅ (ℕ → E)` for *any*
preordered `E`, order-isomorphically. Transporting along `iterSeqEquiv` turns this into
`(iterSys V).Element × (iterSys V).Element ≃o (iterSys V).Element` for any `V`, i.e.
`iterSys V × iterSys V ≅ᴰ iterSys V`. Specializing `V := 𝒰` gives the required `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-! ### Generic order-isomorphism lemmas about `Pi`/`Prod` types -/


/-! ### `𝒟^∞ × 𝒟^∞ ≅ 𝒟^∞` for every `𝒟`, in particular for `𝒟 = 𝒰` -/

end DomainTheory.NeighbourhoodSystems
