module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_inter_nonempty_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.isomorphic_tokenSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.principal_mem_bracket

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem theorem_110.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX)) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y)))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket_inter_nonempty_iff
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket_inter)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isomorphic_tokenSystem)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal_mem_bracket

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
