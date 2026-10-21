/-ai
The next projection equals the structure isomorphism of the colimit composed after the image under T of the current projection composed after the inverse isomorphism.

The two components of the colimit isomorphism are the components of the identity isomorphism of the object equality. Conjugation by that isomorphism is transport along the equality. Heterogeneous equality then identifies the transport with the next projection, using the heterogeneous equality of the image of the projection with the next projection and the lemma that transport along an object equality is a heterogeneous equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.transport_heq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.isoOfEq_conj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.map_rho_heq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}













































/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the structure iso). Since the
iso `𝒟 ≅ T(𝒟)` is the identity, this is the carrier transport of `T(ρₙ)`; combined with
`map_rho_heq` it pins `ρₙ₊₁`. -/
theorem key_rho (s : Setup.{w}) (n : ℕ) :
    rho s (n + 1) = (colimIso s).hom ⊚ Tmap_rho s n ⊚ (colimIso s).inv := by
  rw [show (colimIso s).hom = (isoOfEq (colimObj_eq s)).hom from rfl,
      show (colimIso s).inv = (isoOfEq (colimObj_eq s)).inv from rfl,
      isoOfEq_conj (colimObj_eq s) (Tmap_rho s n)]
  apply eq_of_heq
  exact HEq.trans (map_rho_heq s n).symm
    (transport_heq (colimObj_eq s) (Tmap_rho s n)).symm

end Theorem614
end DomainTheory.NeighbourhoodSystems
