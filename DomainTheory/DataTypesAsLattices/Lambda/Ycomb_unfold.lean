/-ai
Scott's unfolding of equation (2.8) states that the application of Y at u equals the application of u to the application of Y at u.

The application law for Y rewrites the left side as the application of omega(u) to itself. The application law for omega rewrites that as the application of u to the same diagonal. Rewriting the diagonal by the application law for Y gives the application of u to the application of Y at u.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb_app
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















































/-- **Scott 1976, (2.8) unfolding.** `Y(u) = u(Y(u))`. -/
theorem Ycomb_unfold (u : Pomega) :
    funOf Ycomb u = funOf u (funOf Ycomb u) := by
  calc
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) := Ycomb_app u
    _ = funOf u (funOf (omegaComb u) (omegaComb u)) :=
      omegaComb_app u (omegaComb u)
    _ = funOf u (funOf Ycomb u) := by rw [Ycomb_app]

end DomainTheory.DataTypesAsLattices
