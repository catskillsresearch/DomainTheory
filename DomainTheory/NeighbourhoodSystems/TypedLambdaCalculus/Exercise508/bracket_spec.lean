/-ai
The denotation of the bracket abstraction of an open term, applied to any element, equals the denotation of the term at that element. Thus every lambda-abstraction is denoted by a variable-free expression built from I, K, S, and the constants of the term, using only application.

The proof is by induction on the term. The variable simplifies to the identity combinator, and its value equation returns the element. A constant simplifies to K applied to that constant, and its value equation returns the constant. An application simplifies to S applied to the two abstractions, and the value equation of S, rewritten by the two inductive hypotheses, returns the application of the denotations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Ielem_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Kelem_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Selem_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


variable {α β γ : Type*}


variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}


/-- **Combinatory completeness (Exercise 5.8, Scott 1981, PRG-19).** The variable-free combinator
expression `bracket t` denotes exactly the function `λx.t`: applied to any `x`, it yields `t.denote x`.

Thus, with `I`, `K`, `S` (and the constants of `t`) available, every `λ`-abstraction can be defined
by combining combinators using application as the only mode of combination — Scott's "turning of the
tables". -/
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

end DomainTheory.NeighbourhoodSystems.Exercise508
