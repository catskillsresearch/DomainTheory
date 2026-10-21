/-ai
Scott's domain C of finite or infinite binary sequences is isomorphic to the three-way separated sum of the one-point domain with two copies of C. A sequence is bottom, the finished empty sequence, or begins with 0 or with 1.

The isomorphism is ccEquiv.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62








variable {α β γ : Type*}



























variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)


variable {V₀ V₁ V₂}











namespace Example62C





























/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `C ≅ {{Λ}} + C + C`.** Scott's domain
`C` of finite-or-infinite binary sequences is, as a domain, isomorphic to the three-way separated sum
`𝟙 + C + C`: a sequence is bottom, the finished empty sequence `Λ` (the `𝟙` summand), or begins with
`0` or `1` (the two `C` summands). -/
theorem C_domain_equation :
    C ≅ᴰ sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty :=
  ⟨ccEquiv⟩

end Example62C
end DomainTheory.NeighbourhoodSystems
