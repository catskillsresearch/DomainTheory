/-ai
If an endomap of the universal domain is a finitary projection, then its sharp is a finitary projection. If an endomap a is a retraction, then so is the catamorphism that recurses a on the leaves of the tree algebra and uses the algebra's own pairing on nodes. If an endomap a of the universal domain is a retraction, then its inner sharp is a retraction. If an endomap of the universal domain is a projection, then its sharp is a projection. If the inner sharp of an endomap of the universal domain is a retraction, then the sharp of that endomap is a retraction.

The numbered name example_821 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.isFinitaryProjection_aSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharpInner_idem_of_isRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.isProjection_aSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.isRetraction_aSharp

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

end DomainTheory.NeighbourhoodSystems
