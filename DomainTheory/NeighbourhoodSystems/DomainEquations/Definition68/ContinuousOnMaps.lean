/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor_map

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

/-- **Definition 6.8 (Scott 1981, PRG-19).** An endofunctor `T` on the category of domains is
*continuous on maps* when, for every pair of domains `D` and `E`, the induced action `λf. T(f)` on the
**strict** function space `(D →⊥ E)` is approximable: there is an approximable map `Φ` from
`(D →⊥ E)` to `(T(D) →⊥ T(E))` whose elementwise action (read through the representation
`strictFunEquiv`) sends each strict map `f` to `T(f)`. -/
def ContinuousOnMaps (T : Endofunctor DomainObj) : Prop :=
  ∀ D E : DomainObj,
    ∃ Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys),
      ∀ f : StrictMap D.sys E.sys,
        (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1

end DomainTheory.NeighbourhoodSystems
