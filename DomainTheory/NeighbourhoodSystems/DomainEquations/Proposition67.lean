module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.str_comp_desc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}


end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_67.{u, u_1} : ∀ {Obj : Type u} [inst : CategoryTheory.Category.{u_1, u} Obj]
  {T : @DomainTheory.NeighbourhoodSystems.Endofunctor Obj inst}
  (A : @DomainTheory.NeighbourhoodSystems.TAlgebra Obj inst T)
  (hA : @DomainTheory.NeighbourhoodSystems.IsInitial Obj inst T A),
  @Eq
    (@Quiver.Hom Obj (@CategoryTheory.CategoryStruct.toQuiver Obj (@CategoryTheory.Category.toCategoryStruct Obj inst))
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A))
    (@DomainTheory.NeighbourhoodSystems.compAfter Obj inst
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj Obj inst T
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A))
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.str Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.AlgHom.hom Obj inst T A (@DomainTheory.NeighbourhoodSystems.tStr Obj inst T A)
        (@DomainTheory.NeighbourhoodSystems.IsInitial.desc Obj inst T A hA
          (@DomainTheory.NeighbourhoodSystems.tStr Obj inst T A))))
    (@CategoryTheory.CategoryStruct.id Obj (@CategoryTheory.Category.toCategoryStruct Obj inst)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)) :=
  @DomainTheory.NeighbourhoodSystems.str_comp_desc

end DomainTheory.NeighbourhoodSystems
