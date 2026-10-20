/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612

@[expose] public section

universe w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Definition 6.13, monotone part (pointwise).** Given a subdomain relation `h : D ◁ E`, the data
witnessing that the functor `T` carries it to `T(D) ◁ T(E)` *and* carries the projection pair `i, j`
of 6.12 to the projection pair of `T(D) ◁ T(E)`.

Because `T` may change the token type, the two image systems live a priori over different carriers;
`carrier_eq` records that they coincide, `sub` is the resulting subdomain relation (with `T(E)`'s
system transported into `T(D)`'s carrier), and `inj_heq`/`proj_heq` say the canonical 6.12 maps of
`sub` are `T(i)` and `T(j)` (up to that transport, hence `HEq`). -/
structure MonotoneAt (T : Endofunctor DomainObj.{w}) {α : Type w}
    {D E : NeighborhoodSystem α} (h : D ◁ E) : Prop where
  /-- The two image carriers coincide, so `T(D) ◁ T(E)` can be stated. -/
  carrier_eq : (T.obj ⟨α, E⟩).carrier = (T.obj ⟨α, D⟩).carrier
  /-- The image subdomain relation `T(D) ◁ T(E)` (with `T(E)`'s system carried into `T(D)`'s
  carrier). -/
  sub : (T.obj ⟨α, D⟩).sys ◁
    (carrier_eq ▸ (T.obj ⟨α, E⟩).sys : NeighborhoodSystem (T.obj ⟨α, D⟩).carrier)
  /-- The injection of `T(D) ◁ T(E)` is `T(i)` (Scott: the pair is mapped to `T(i), T(j)`). -/
  inj_heq : HEq (T.map (X := ⟨α, D⟩) (Y := ⟨α, E⟩) h.inj) sub.inj
  /-- The projection of `T(D) ◁ T(E)` is `T(j)`. -/
  proj_heq : HEq (T.map (X := ⟨α, E⟩) (Y := ⟨α, D⟩) h.proj) sub.proj

end DomainTheory.NeighbourhoodSystems
