/-ai
U is isomorphic to V as domains.

The effective isomorphism of U with V converts to a domain isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem













/-- **Exercise 8.13(a).** `U` is isomorphic to `V`'s domain of elements, and `V`'s domain of
elements is (`V_mem_iff_generatedBy`, `generators_independent`) *by construction* the domain of
proper filters of the free Boolean algebra on `ℵ₀` generators. No new back-and-forth argument is
needed: `effectiveIso812_UV` (`Exercise812g4.lean`, already `Pass`) already supplies the
isomorphism (in fact an *effective* one, stronger than what `8.13` asks for). -/
theorem exercise813a : U ≅ᴰ V := ⟨effectiveIso812_UV.toDomainIso⟩

end DomainTheory.NeighbourhoodSystems
