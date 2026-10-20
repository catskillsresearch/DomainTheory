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
