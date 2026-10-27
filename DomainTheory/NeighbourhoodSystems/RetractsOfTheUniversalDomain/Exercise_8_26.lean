module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UapplyUlam

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 8.26 (Scott 1981, PRG-19).** Self-application of self-abstraction recovers the map:
`Uapply (Ulam f) x = f(x)`. -/
theorem exercise_8_26 (f : ApproximableMap U U) (x : U.Element) :
    Uapply (Ulam f) x = f.toElementMap x :=
  Uapply_Ulam f x

end
