/-ai
The composite of a homomorphism from the colimit algebra with the next projection equals the structure map of the target, composed after the image under T of the previous composite, composed after the inverse of the colimit isomorphism.

The next projection is replaced, by the key identity, with the structure isomorphism composed after the image of the current projection composed after the inverse. Associativity moves the structure isomorphism beside the homomorphism, the homomorphism square replaces that pair by the structure map of the target composed after the image of the homomorphism, and a further association together with functoriality of T reassembles the image of the composite with the projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.key_rho

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}















































/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`.** Using `key_rho` (`ρₙ₊₁ = i∘T(ρₙ)∘j`) and the
homomorphism square `g ∘ i = k ∘ T(g)`. -/
theorem gcomp_rho_succ (s : Setup.{w}) (B : TAlgebra s.T) (g : AlgHom (colimAlg s) B) (n : ℕ) :
    g.hom.comp (rho s (n + 1))
      = B.str.comp ((s.T.map (X := objColim s) (Y := B.carrier)
          (g.hom.comp (rho s n))).comp (colimIso s).inv) := by
  have hcomm : g.hom ⊚ (colimIso s).hom
      = B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom := g.comm
  show g.hom ⊚ rho s (n + 1)
      = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)) ⊚ (colimIso s).inv
  calc g.hom ⊚ rho s (n + 1)
      = g.hom ⊚ ((colimIso s).hom ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          congrArg (fun x => g.hom ⊚ x) (key_rho s n)
    _ = (g.hom ⊚ (colimIso s).hom) ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) :=
          CategoryTheory.Category.assoc (Tmap_rho s n ⊚ (colimIso s).inv) (colimIso s).hom g.hom
    _ = (B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) := by rw [hcomm]
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) g.hom
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          (CategoryTheory.Category.assoc (Tmap_rho s n ⊚ (colimIso s).inv)
            (s.T.map (X := objColim s) (Y := B.carrier) g.hom) B.str).symm
    _ = B.str ⊚ ((s.T.map (X := objColim s) (Y := B.carrier) g.hom ⊚ Tmap_rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (B.str ⊚ ·)
            (CategoryTheory.Category.assoc (colimIso s).inv (Tmap_rho s n)
              (s.T.map (X := objColim s) (Y := B.carrier) g.hom))
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (fun m => B.str ⊚ (m ⊚ (colimIso s).inv))
            (s.T.map_comp (X := objColim s) (Y := objColim s) (Z := B.carrier) g.hom
              (rho s n)).symm

end Theorem614
end DomainTheory.NeighbourhoodSystems
