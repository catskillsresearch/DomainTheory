module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.talgebra
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.DomainObj
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.smashProduct

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

universe u

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

structure IsInitial (A : TAlgebra T) where
  desc : (B : TAlgebra T) → AlgHom A B
  uniq : ∀ (B : TAlgebra T) (h : AlgHom A B), h = desc B

namespace AlgHom

variable {T : Endofunctor Obj}

def comp {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) : AlgHom A C where
  hom := β.hom ⊚ α.hom
  comm := by
    have hα := α.comm
    have hβ := β.comm
    have hmap := T.map_comp β.hom α.hom
    dsimp only [compAfter] at hα hβ hmap ⊢
    rw [← CategoryTheory.Category.assoc, hα, CategoryTheory.Category.assoc, hβ,
      ← CategoryTheory.Category.assoc, hmap]

def id (A : TAlgebra T) : AlgHom A A where
  hom := (𝟙 A.carrier)
  comm := by
    simp only [compAfter]
    rw [CategoryTheory.Category.comp_id, T.map_id, CategoryTheory.Category.id_comp]

@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = (𝟙 A.carrier) := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom

def idEndofunctor (Obj : Type u) [Category Obj] : Endofunctor Obj where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem idEndofunctor_obj {Obj : Type u} [Category Obj] (X : Obj) :
    (idEndofunctor Obj).obj X = X := rfl

@[simp] theorem idEndofunctor_map {Obj : Type u} [Category Obj] {X Y : Obj}
    (f : (X ⟶ Y)) : (idEndofunctor Obj).map f = f := rfl

end DomainTheory.NeighbourhoodSystems
