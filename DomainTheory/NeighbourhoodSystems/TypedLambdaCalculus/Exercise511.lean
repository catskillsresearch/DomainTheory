module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.component_diag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.component_map
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.diag_rec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.map_rec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise511

set_option linter.unusedVariables false

theorem example_511.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V) x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
          (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) x
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (s :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
        (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.iterSys α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
        (@DomainTheory.NeighbourhoodSystems.pair (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
          α
          (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
          V s x))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
        (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)
                (@DomainTheory.NeighbourhoodSystems.Exercise511.head
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
            (@DomainTheory.NeighbourhoodSystems.pair
              (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
              (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
              V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.Exercise511.tail
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s)
              x))))) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V) x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
          (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) x
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (s :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
        (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.iterSys α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
        (@DomainTheory.NeighbourhoodSystems.pair (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
          α
          (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
          V s x))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
        (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)
                (@DomainTheory.NeighbourhoodSystems.Exercise511.head
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
            (@DomainTheory.NeighbourhoodSystems.pair
              (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
              (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
              V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.Exercise511.tail
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s)
              x)))))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V) x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
          (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) x
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x))))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x))
      @DomainTheory.NeighbourhoodSystems.Exercise511.component_diag
      @DomainTheory.NeighbourhoodSystems.Exercise511.component_map)
    @DomainTheory.NeighbourhoodSystems.Exercise511.diag_rec)
  @DomainTheory.NeighbourhoodSystems.Exercise511.map_rec

end DomainTheory.NeighbourhoodSystems.Exercise511
