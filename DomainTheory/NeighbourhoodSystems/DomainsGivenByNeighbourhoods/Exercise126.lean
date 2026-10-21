/-ai
If two finite sets generate the same ideal, they determine the same neighbourhood I(F).

The numbered name example_126 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_eq_of_span_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Ring

set_option linter.unusedVariables false

theorem example_126.{u_1} : ∀ {A : Type u_1} [inst : CommRing A] {F₁ F₂ : Finset A},
  @Eq (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
      (@Ideal.span A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A) F₁))
      (@Ideal.span A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A) F₂)) →
    @Eq (Set (Finset A)) (@DomainTheory.NeighbourhoodSystems.Ring.IFamily A inst F₁)
      (@DomainTheory.NeighbourhoodSystems.Ring.IFamily A inst F₂) :=
  @DomainTheory.NeighbourhoodSystems.Ring.IFamily_eq_of_span_eq

end DomainTheory.NeighbourhoodSystems.Ring
