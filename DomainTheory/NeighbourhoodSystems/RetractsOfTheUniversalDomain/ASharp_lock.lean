module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp_more

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_821.{u_1} : And
  (And
    (And
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a)))
    (∀
      {a :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.aSharp a)))
  (∀
    {a :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
        (DomainTheory.NeighbourhoodSystems.aSharpInner a) →
      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.aSharp a)) :=
  @And.intro
  (And
    (And
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a)))
    (∀
      {a :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.aSharp a)))
  (∀
    {a :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
        (DomainTheory.NeighbourhoodSystems.aSharpInner a) →
      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.aSharp a))
  (@And.intro
    (And
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a)))
    (∀
      {a :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.aSharp a))
    (@And.intro
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a))
      (@And.intro
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
        @DomainTheory.NeighbourhoodSystems.isFinitaryProjection_aSharp
        @DomainTheory.NeighbourhoodSystems.gMap_selfComp_eq_of_isRetraction)
      @DomainTheory.NeighbourhoodSystems.aSharpInner_idem_of_isRetraction)
    @DomainTheory.NeighbourhoodSystems.isProjection_aSharp)
  @DomainTheory.NeighbourhoodSystems.isRetraction_aSharp


theorem example_825_congr.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
  (V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ),
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₂)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
      V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
    (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)) :=
  @DomainTheory.NeighbourhoodSystems.curry_isomorphic


theorem example_825_closing.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
  @DomainTheory.NeighbourhoodSystems.Isomorphic α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β D V) D
      (@DomainTheory.NeighbourhoodSystems.funSpace α β D V) →
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum β β) β (@DomainTheory.NeighbourhoodSystems.prod β β V V) V →
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D) :=
  @DomainTheory.NeighbourhoodSystems.funSpace_self_isomorphic


end DomainTheory.NeighbourhoodSystems
