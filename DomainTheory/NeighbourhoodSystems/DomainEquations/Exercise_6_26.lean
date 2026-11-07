module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.liftDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem BitDom
open DomainTheory.NeighbourhoodSystems.FunctorTokens
theorem example_626 :
    (∀ {D : NeighborhoodSystem Str} {hD : ∀ X, D.mem X → X.Nonempty} (z : (liftTok D hD).Element),
        z = liftBot D hD ∨ ∃ x : D.Element, z = liftUp (hD := hD) x) ∧
    (∀ {D E : ScottSys}, (D.lift.oplus E.lift).sys ≅ᴰ (D.sum E).sys) ∧
    (∀ {D E : ScottSys}, (D.lift.otimes E.lift).sys ≅ᴰ (D.prod E).lift.sys) :=
  ⟨@eq_liftBot_or_exists_liftUp, @lift_oplus_lift_iso_sum, @lift_otimes_lift_iso_lift_prod⟩

