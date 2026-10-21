/-ai
The post- and pre-composition operator is the approximable map of strict function spaces sending a strict map g from T(D) to T(E) to the strict map k composed with g composed with j. It is the monotone extension of the assignment that sends a finite neighbourhood to the strict filter of that composite applied to the principal strict map of the neighbourhood. The assignment is monotone because the strict filter, the composite, and the strict representation are monotone, and principal neighbourhoods are ordered by inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.toStrictMap_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.toStrictFilter_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.homOpComp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.homOpComp_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)

/-- **The operator `λg. k ∘ g ∘ j`** as an approximable map between the strict function spaces, built
by Exercise 2.8 (`ofMono`) from its values on finite elements. -/
def homOp : ApproximableMap (strictFun (T.obj D).sys (T.obj E).sys) (strictFun D.sys E.sys) :=
  ofMono
    (fun N hN => toStrictFilter (homOpComp T D E j k hj hk
      (toStrictMap ((strictFun (T.obj D).sys (T.obj E).sys).principal hN))))
    (by
      intro N N' hN hN' hN'N
      apply toStrictFilter_mono
      apply homOpComp_mono
      apply toStrictMap_mono
      exact ((strictFun (T.obj D).sys (T.obj E).sys).principal_le_iff hN hN').mpr hN'N)

end HomOp

end DomainTheory.NeighbourhoodSystems
