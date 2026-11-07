module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UapplyUlam

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem example_826 (f : ApproximableMap U U) (x : U.Element) :
    Uapply (Ulam f) x = f.toElementMap x :=
  Uapply_Ulam f x

