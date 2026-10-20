/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise508.Basic
import DomainTheory.Neighborhood.Exercise508.Ielem_apply
import DomainTheory.Neighborhood.Exercise508.Kelem_apply
import DomainTheory.Neighborhood.Exercise508.Selem_apply


namespace DomainTheory.Neighborhood.Exercise508

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap


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

end DomainTheory.Neighborhood.Exercise508
