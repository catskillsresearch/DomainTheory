module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iotimes_only_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iotimes_subsingleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.isum_summand_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.isum_trichotomy

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise629

set_option linter.unusedVariables false

theorem example_629.{u, v} : And
  (And
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j))
  (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
    {hne :
      ∀ (i : ι) (X : Set (α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
    (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
        (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)),
    Or
      (∃ (i : ι) (X : Set (α i)),
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X)))
      (∀ (W : Set (Option (@Sigma ι fun (i : ι) => α i))),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z W →
          @Eq (Set (Option (@Sigma ι fun (i : ι) => α i))) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (Option (@Sigma ι fun (i : ι) => α i))
              (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)))) :=
  @And.intro
  (And
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j))
  (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
    {hne :
      ∀ (i : ι) (X : Set (α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
    (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
        (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)),
    Or
      (∃ (i : ι) (X : Set (α i)),
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X)))
      (∀ (W : Set (Option (@Sigma ι fun (i : ι) => α i))),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z W →
          @Eq (Set (Option (@Sigma ι fun (i : ι) => α i))) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (Option (@Sigma ι fun (i : ι) => α i))
              (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))))
  (@And.intro
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j)
    (@And.intro
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      @DomainTheory.NeighbourhoodSystems.Exercise629.iotimes_only_master
      @DomainTheory.NeighbourhoodSystems.Exercise629.iotimes_subsingleton)
    @DomainTheory.NeighbourhoodSystems.Exercise629.isum_summand_unique)
  @DomainTheory.NeighbourhoodSystems.Exercise629.isum_trichotomy

end DomainTheory.NeighbourhoodSystems.Exercise629
