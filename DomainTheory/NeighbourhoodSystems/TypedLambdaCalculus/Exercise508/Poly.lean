/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `Poly X A`: an open term of type `A` with a single free variable of type `X`. Constructors:
the variable, a closed constant (any element of any domain — "enough combinators available"), and
application. This is the syntax of `λ`-bodies whose abstraction we want to eliminate. -/
inductive Poly (X : Dom) : Dom → Type 1 where
  | var : Poly X X
  | con {A : Dom} (c : A.sys.Element) : Poly X A
  | app {A B : Dom} (f : Poly X (A.arrow B)) (a : Poly X A) : Poly X B


/-- The denotation of an open term: the body as a function of its free variable. -/
def Poly.denote {X : Dom} : {A : Dom} → Poly X A → X.sys.Element → A.sys.Element
  | _, .var, x => x
  | _, .con c, _ => c
  | _, .app f a, x => (toApproxMap (f.denote x)).toElementMap (a.denote x)

end DomainTheory.NeighbourhoodSystems.Exercise508
