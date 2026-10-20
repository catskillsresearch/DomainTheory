module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Poly
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.CL
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Ielem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Kelem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Selem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- **Bracket abstraction.** Turn an open body `t` (a `λ`-body with one free variable) into a
*variable-free* combinator expression denoting `λx.t`, using only application and the combinators
`I`, `K`, `S` together with the constants already occurring in `t`:

* `[x] x        = I`
* `[x] c        = K(c)`           (`c` a constant / closed term)
* `[x] (f a)    = S([x]f)([x]a)`.
-/
def bracket {X : Dom} : {A : Dom} → Poly X A → CL (X.arrow A)
  | _, .var => .con (Ielem X)
  | _, .con c => .app (.con (Kelem _ X)) (.con c)
  | _, .app f a => .app (.app (.con (Selem X _ _)) (bracket f)) (bracket a)

end DomainTheory.NeighbourhoodSystems.Exercise508
