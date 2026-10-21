/-ai
The catamorphism relation of an approximable map u from the base domain into the target and an approximable map v from the product of the target with itself into the target holds in one of three ways. The master neighbourhood of the sharp domain is related only to the master neighbourhood of the target. The zero embedding of a neighbourhood X is related to Z when u relates X to Z. The paired embedding of P and Q is related to Z when P is related to some Z₁, Q is related to some Z₂, and v relates the product of Z₁ and Z₂ to Z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

/-- **The universal strict map `g : D^§ → E`, as a neighbourhood relation.** Defined by recursion on
the `D^§`-neighbourhood shape: `Γ ↦ Δ_E`, `0·X ↦ u`'s relation, `1·P∪2·Q ↦ v ∘ (g × g)`. -/
inductive GRel (u : ApproximableMap D E) (v : ApproximableMap (prod E E) E) :
    Set (List Bool × α) → Set β → Prop
  | gamma {Z} : Z = E.master → GRel u v (Gamma D) Z
  | leaf {X Z} : u.rel X Z → GRel u v (embZero X) Z
  | node {P Q Z₁ Z₂ Z} : GRel u v P Z₁ → GRel u v Q Z₂ →
      v.rel (prodNbhd Z₁ Z₂) Z → GRel u v (embPair P Q) Z

end Exercise717
end DomainTheory.NeighbourhoodSystems
