module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise508
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

structure Dom where

  carrier : Type

  sys : NeighborhoodSystem carrier

abbrev Dom.arrow (A B : Dom) : Dom := ⟨ApproximableMap A.sys B.sys, funSpace A.sys B.sys⟩

inductive CL : Dom → Type 1 where
  | con {A : Dom} (c : A.sys.Element) : CL A
  | app {A B : Dom} (f : CL (A.arrow B)) (a : CL A) : CL B

def CL.denote : {A : Dom} → CL A → A.sys.Element
  | _, .con c => c
  | _, .app f a => (toApproxMap f.denote).toElementMap a.denote

inductive Poly (X : Dom) : Dom → Type 1 where
  | var : Poly X X
  | con {A : Dom} (c : A.sys.Element) : Poly X A
  | app {A B : Dom} (f : Poly X (A.arrow B)) (a : Poly X A) : Poly X B

def Poly.denote {X : Dom} : {A : Dom} → Poly X A → X.sys.Element → A.sys.Element
  | _, .var, x => x
  | _, .con c, _ => c
  | _, .app f a, x => (toApproxMap (f.denote x)).toElementMap (a.denote x)

def Ielem (X : Dom) : (X.arrow X).sys.Element := toFilter (idMap X.sys)

def Kelem (A X : Dom) : (A.arrow (X.arrow A)).sys.Element := toFilter (curry (proj₀ A.sys X.sys))

def Sbody (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap
      (prod (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx) Vb :=
  (evalMap Va Vb).comp
    (paired
      ((evalMap Vx (funSpace Va Vb)).comp
        (paired
          ((proj₀ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx)))
      ((evalMap Vx Va).comp
        (paired
          ((proj₁ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))))

def Smap (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap (funSpace Vx (funSpace Va Vb))
      (funSpace (funSpace Vx Va) (funSpace Vx Vb)) :=
  curry (curry (Sbody Vx Va Vb))

def Selem (X A B : Dom) :
    ((X.arrow (A.arrow B)).arrow ((X.arrow A).arrow (X.arrow B))).sys.Element :=
  toFilter (Smap X.sys A.sys B.sys)

def bracket {X : Dom} : {A : Dom} → Poly X A → CL (X.arrow A)
  | _, .var => .con (Ielem X)
  | _, .con c => .app (.con (Kelem _ X)) (.con c)
  | _, .app f a => .app (.app (.con (Selem X _ _)) (bracket f)) (bracket a)

theorem Smap_apply (F : (funSpace Vx (funSpace Va Vb)).Element) (G : (funSpace Vx Va).Element)
    (x : Vx.Element) :
    (toApproxMap ((toApproxMap ((Smap Vx Va Vb).toElementMap F)).toElementMap G)).toElementMap x
      = (toApproxMap ((toApproxMap F).toElementMap x)).toElementMap ((toApproxMap G).toElementMap x) := by
  rw [Smap, toElementMap_curry_apply, toElementMap_curry_apply]
  simp only [Sbody, toElementMap_comp, toElementMap_paired, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]
end

section
variable {α β γ : Type*}

theorem toApproxMap_toFilter {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (f : ApproximableMap V₀ V₁) : toApproxMap (toFilter f) = f := by
  have he := (funSpaceEquiv V₀ V₁).apply_symm_apply f
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

theorem Ielem_apply (X : Dom) (x : X.sys.Element) :
    (toApproxMap (Ielem X)).toElementMap x = x := by
  rw [Ielem, toApproxMap_toFilter, toElementMap_idMap]

theorem Kelem_apply (A X : Dom) (c : A.sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap (Kelem A X)).toElementMap c)).toElementMap x = c := by
  rw [Kelem, toApproxMap_toFilter]
  have h := toElementMap_curry_apply (proj₀ A.sys X.sys) c x
  rw [toElementMap_proj₀, fst_pair] at h
  exact h

theorem Selem_apply (X A B : Dom)
    (F : (X.arrow (A.arrow B)).sys.Element) (G : (X.arrow A).sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap ((toApproxMap (Selem X A B)).toElementMap F)).toElementMap G)).toElementMap x
      = (toApproxMap ((toApproxMap F).toElementMap x)).toElementMap ((toApproxMap G).toElementMap x) := by
  rw [Selem, toApproxMap_toFilter]
  exact Smap_apply F G x
end
end DomainTheory.NeighbourhoodSystems.Exercise508

section
namespace DomainTheory.NeighbourhoodSystems.Exercise508
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

theorem bracket_spec {X : Dom} {A : Dom} (t : Poly X A) (x : X.sys.Element) :
    (toApproxMap (bracket t).denote).toElementMap x = t.denote x := by
  induction t with
  | var =>
      simp only [bracket, CL.denote, Poly.denote]
      exact Ielem_apply X x
  | @con A c =>
      simp only [bracket, CL.denote, Poly.denote]
      exact Kelem_apply A X c x
  | @app A B f a ihf iha =>
      simp only [bracket, CL.denote, Poly.denote]
      have hS := Selem_apply X A B (CL.denote (bracket f)) (CL.denote (bracket a)) x
      rw [ihf, iha] at hS
      exact hS
end

end DomainTheory.NeighbourhoodSystems.Exercise508
end
