/-ai
Every countable neighbourhood system D is isomorphic to some neighbourhood system D' of subsets of the rationals, and D' is a subsystem of the universal system U. If D is effectively given, there is a neighbourhood system of sets of rationals which is itself effectively given, isomorphic to D, and a subsystem of the universal system, and whose injection into the universal system and projection back are computable relative to the two presentations. Theorem 8.8(c) of Scott (1981, PRG-19).

The numbered name theorem_88 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88g.theorem_8_8_b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88m.theorem_8_8_c

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_88.{u, u_1} : And
  (And
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      [Countable (@Subtype (Set α) fun (S : Set α) => @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D S)],
      ∃ (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem Rat),
        And (@DomainTheory.NeighbourhoodSystems.Isomorphic α Rat D D')
          (@DomainTheory.NeighbourhoodSystems.Subsystem Rat D' DomainTheory.NeighbourhoodSystems.U))
    (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
      ∃ (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem Rat) (P' :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation Rat D') (h :
        @DomainTheory.NeighbourhoodSystems.Subsystem Rat D' DomainTheory.NeighbourhoodSystems.U),
        And (@DomainTheory.NeighbourhoodSystems.Isomorphic α Rat D D')
          (And
            (@DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat D' DomainTheory.NeighbourhoodSystems.U P'
              DomainTheory.NeighbourhoodSystems.UComputablePresentation
              (@DomainTheory.NeighbourhoodSystems.Subsystem.inj Rat D' DomainTheory.NeighbourhoodSystems.U h))
            (@DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat DomainTheory.NeighbourhoodSystems.U D'
              DomainTheory.NeighbourhoodSystems.UComputablePresentation P'
              (@DomainTheory.NeighbourhoodSystems.Subsystem.proj Rat D' DomainTheory.NeighbourhoodSystems.U h)))))
  (∀
    {a :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @DomainTheory.NeighbourhoodSystems.IsFinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
      @DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.UComputablePresentation
          DomainTheory.NeighbourhoodSystems.UComputablePresentation a →
        And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven Rat
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U a))
          (@DomainTheory.NeighbourhoodSystems.Subsystem Rat
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U a)
            DomainTheory.NeighbourhoodSystems.U)) :=
  @And.intro
  (And
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      [Countable (@Subtype (Set α) fun (S : Set α) => @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D S)],
      ∃ (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem Rat),
        And (@DomainTheory.NeighbourhoodSystems.Isomorphic α Rat D D')
          (@DomainTheory.NeighbourhoodSystems.Subsystem Rat D' DomainTheory.NeighbourhoodSystems.U))
    (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
      ∃ (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem Rat) (P' :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation Rat D') (h :
        @DomainTheory.NeighbourhoodSystems.Subsystem Rat D' DomainTheory.NeighbourhoodSystems.U),
        And (@DomainTheory.NeighbourhoodSystems.Isomorphic α Rat D D')
          (And
            (@DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat D' DomainTheory.NeighbourhoodSystems.U P'
              DomainTheory.NeighbourhoodSystems.UComputablePresentation
              (@DomainTheory.NeighbourhoodSystems.Subsystem.inj Rat D' DomainTheory.NeighbourhoodSystems.U h))
            (@DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat DomainTheory.NeighbourhoodSystems.U D'
              DomainTheory.NeighbourhoodSystems.UComputablePresentation P'
              (@DomainTheory.NeighbourhoodSystems.Subsystem.proj Rat D' DomainTheory.NeighbourhoodSystems.U h)))))
  (∀
    {a :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @DomainTheory.NeighbourhoodSystems.IsFinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
      @DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.UComputablePresentation
          DomainTheory.NeighbourhoodSystems.UComputablePresentation a →
        And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven Rat
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U a))
          (@DomainTheory.NeighbourhoodSystems.Subsystem Rat
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U a)
            DomainTheory.NeighbourhoodSystems.U))
  (@And.intro
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      [Countable (@Subtype (Set α) fun (S : Set α) => @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D S)],
      ∃ (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem Rat),
        And (@DomainTheory.NeighbourhoodSystems.Isomorphic α Rat D D')
          (@DomainTheory.NeighbourhoodSystems.Subsystem Rat D' DomainTheory.NeighbourhoodSystems.U))
    (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
      ∃ (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem Rat) (P' :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation Rat D') (h :
        @DomainTheory.NeighbourhoodSystems.Subsystem Rat D' DomainTheory.NeighbourhoodSystems.U),
        And (@DomainTheory.NeighbourhoodSystems.Isomorphic α Rat D D')
          (And
            (@DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat D' DomainTheory.NeighbourhoodSystems.U P'
              DomainTheory.NeighbourhoodSystems.UComputablePresentation
              (@DomainTheory.NeighbourhoodSystems.Subsystem.inj Rat D' DomainTheory.NeighbourhoodSystems.U h))
            (@DomainTheory.NeighbourhoodSystems.IsComputableMap Rat Rat DomainTheory.NeighbourhoodSystems.U D'
              DomainTheory.NeighbourhoodSystems.UComputablePresentation P'
              (@DomainTheory.NeighbourhoodSystems.Subsystem.proj Rat D' DomainTheory.NeighbourhoodSystems.U h))))
    @DomainTheory.NeighbourhoodSystems.theorem_8_8_a @DomainTheory.NeighbourhoodSystems.theorem_8_8_b)
  @DomainTheory.NeighbourhoodSystems.theorem_8_8_c

end DomainTheory.NeighbourhoodSystems
