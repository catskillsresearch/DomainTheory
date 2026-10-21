/-ai
This file gathers and re-exports Lambek's lemma, Proposition 6.7: the structure map of an initial algebra is an isomorphism from the image of the carrier to the carrier. It brings together the algebra obtained by applying the endofunctor to the structure map, the homomorphism property of that structure map, and the identity law for its composite with the homomorphism given by initiality.

The structure map of an initial T-algebra, composed with the descent homomorphism into the algebra given by applying T to the structure map, is the identity on the carrier.

The numbered name theorem_67 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.str_comp_desc

@[expose] public section

/-!
# Lecture VI — Proposition 6.7 (Scott 1981, PRG-19): Lambek's lemma

**Proposition 6.7.** If `i : T(D) → D` is an initial `T`-algebra, then so is `T(i) : T²(D) → T(D)`
and `i` is the isomorphism from `T(D)` to `D`.

We formalise the second (and decisive) half: the structure map of an initial algebra is an
isomorphism. Writing `A = (D, i)`, the functor turns `i` into a new algebra `(T(D), T(i))` (`tStr`),
and `i` itself is a homomorphism `(T(D), T(i)) → (D, i)` (`strHom`). Initiality supplies a
homomorphism `j : (D,i) → (T(D),T(i))`, and the composite `i ∘ j : (D,i) → (D,i)` must be the
identity (`str_comp_desc`). Functoriality then gives `T(i) ∘ T(j) = T(i ∘ j) = I`, and the
homomorphism square for `j` yields `j ∘ i = I`. Hence `i` and `j` are mutually inverse: `i` is an
isomorphism (`lambek`).

This is exactly Scott's remark that "if we are going to have initial algebras at all we have to
satisfy the domain equation `D ≅ T(D)`".

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

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
