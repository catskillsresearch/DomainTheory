module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.subApprox
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DprimeU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Domain.Recursive

theorem theorem_86 :
    (∀ {α : Type*} {E : NeighborhoodSystem α} {f : ApproximableMap E E},
      sub f = f ↔ FinitaryProjection f) ∧
    (∀ {α : Type*} {E : NeighborhoodSystem α}, IsFinitary (subApprox (E := E))) ∧
    (∀ {α : Type*} {E : NeighborhoodSystem α}, FinitaryProjection (subApprox (E := E))) :=
  ⟨@sub_eq_self_iff_isFinitaryProjection, @subApprox.isFinitary,
    @Sub8_6.isFinitaryProjection_subApprox⟩

theorem theorem_86_c :
    (∀ {α : Type*} {E : NeighborhoodSystem α}
      (P : ComputablePresentation E) (gN : ℕ → ℕ)
      (hgN : ∀ c, gN c = 1 ↔
        (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)
      (incl eq : ℕ → ℕ) (hgNp : Nat.Primrec gN)
      (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
      (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq),
      ComputableMap
        (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
        (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
        (subApprox (E := E))) ∧
    (∀ {α : Type*} {E : NeighborhoodSystem α},
      E.IsEffectivelyGiven →
        ∃ Pfun : ComputablePresentation (funSpace E E),
          ComputableMap Pfun Pfun (subApprox (E := E))) :=
  ⟨@subApprox_isComputable, @sub_isComputable_of_isEffectivelyGiven⟩

end DomainTheory.NeighbourhoodSystems
