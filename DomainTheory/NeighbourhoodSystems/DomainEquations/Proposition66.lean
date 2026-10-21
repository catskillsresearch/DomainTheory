/-ai
The homomorphism from an initial algebra A to an algebra B that realises their isomorphism is the only homomorphism from A to B.

The numbered name theorem_66 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition66.iso_hom_unique

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_66.{u, u_1} : ∀ {Obj : Type u} [inst : CategoryTheory.Category.{u_1, u} Obj]
  {T : @DomainTheory.NeighbourhoodSystems.Endofunctor Obj inst}
  {A B : @DomainTheory.NeighbourhoodSystems.TAlgebra Obj inst T}
  (hA : @DomainTheory.NeighbourhoodSystems.IsInitial Obj inst T A)
  (h : @DomainTheory.NeighbourhoodSystems.AlgHom Obj inst T A B),
  @Eq (@DomainTheory.NeighbourhoodSystems.AlgHom Obj inst T A B) h
    (@DomainTheory.NeighbourhoodSystems.IsInitial.desc Obj inst T A hA B) :=
  @DomainTheory.NeighbourhoodSystems.iso_hom_unique

end DomainTheory.NeighbourhoodSystems
