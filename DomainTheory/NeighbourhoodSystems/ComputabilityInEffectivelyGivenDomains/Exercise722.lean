/-ai
The embedding of a concatenation of words is the product of the embeddings. If one word lies in a language and another lies in a second language, their concatenation lies in the concatenation of the languages. The infinite word of a word equals its square.

The numbered name example_722 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.emb_mul
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamArrow_mul_self

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722 : And
  (And
    (∀ (σ τ : List Bool),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.emb
          (@HAppend.hAppend (List Bool) (List Bool) (List Bool)
            (@instHAppendOfAppend (List Bool) (@List.instAppend Bool)) σ τ))
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem (DomainTheory.NeighbourhoodSystems.Exercise722.emb σ)
          (DomainTheory.NeighbourhoodSystems.Exercise722.emb τ)))
    (∀
      (x y z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x y) z)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem y z))))
  (∀ (σ : List Bool),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
        DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
      (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ)
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ))
      (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ)) :=
  @And.intro
  (And
    (∀ (σ τ : List Bool),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.emb
          (@HAppend.hAppend (List Bool) (List Bool) (List Bool)
            (@instHAppendOfAppend (List Bool) (@List.instAppend Bool)) σ τ))
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem (DomainTheory.NeighbourhoodSystems.Exercise722.emb σ)
          (DomainTheory.NeighbourhoodSystems.Exercise722.emb τ)))
    (∀
      (x y z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x y) z)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem y z))))
  (∀ (σ : List Bool),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
        DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
      (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ)
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ))
      (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ))
  (@And.intro
    (∀ (σ τ : List Bool),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.emb
          (@HAppend.hAppend (List Bool) (List Bool) (List Bool)
            (@instHAppendOfAppend (List Bool) (@List.instAppend Bool)) σ τ))
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem (DomainTheory.NeighbourhoodSystems.Exercise722.emb σ)
          (DomainTheory.NeighbourhoodSystems.Exercise722.emb τ)))
    (∀
      (x y z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x y) z)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem y z)))
    DomainTheory.NeighbourhoodSystems.Exercise722.emb_mul DomainTheory.NeighbourhoodSystems.Exercise722.mulElem_assoc)
  DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow_mul_self

end DomainTheory.NeighbourhoodSystems.Exercise722
