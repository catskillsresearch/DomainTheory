module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.exists_algebra_with_hom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.exists_unique_strict_algHom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem614

set_option linter.unusedVariables false

theorem theorem_614.{w} : And
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    ∃ (A :
      @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
      And
        (Nonempty.{w + 1}
          (@DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A))
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A)))
        (∀
          (B :
            @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
          @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
            Nonempty.{w + 1}
              (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A B)))
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    (∀ (X : Set.{w} s.Tok),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem.{w} s.Tok s.Γ X →
          @Eq.{w + 1} (Set.{w} s.Tok) X (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master.{w} s.Tok s.Γ)) →
      ∀
        (B :
          @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
          ∃ (g :
            @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
            And
              (@DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g))
              (∀
                (g' :
                  @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
                @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g') →
                  @Eq.{w + 1}
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B)
                    g' g)) :=
  @And.intro
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    ∃ (A :
      @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
      And
        (Nonempty.{w + 1}
          (@DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A))
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A)))
        (∀
          (B :
            @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
          @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
            Nonempty.{w + 1}
              (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A B)))
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    (∀ (X : Set.{w} s.Tok),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem.{w} s.Tok s.Γ X →
          @Eq.{w + 1} (Set.{w} s.Tok) X (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master.{w} s.Tok s.Γ)) →
      ∀
        (B :
          @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
          ∃ (g :
            @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
            And
              (@DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g))
              (∀
                (g' :
                  @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
                @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g') →
                  @Eq.{w + 1}
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B)
                    g' g))
  DomainTheory.NeighbourhoodSystems.Theorem614.exists_algebra_with_hom.{w}
  DomainTheory.NeighbourhoodSystems.Theorem614.exists_unique_strict_algHom.{w}

end DomainTheory.NeighbourhoodSystems.Theorem614
