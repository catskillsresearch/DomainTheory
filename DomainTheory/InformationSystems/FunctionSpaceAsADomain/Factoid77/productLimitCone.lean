/-ai
The chosen binary-product cone of two information-system objects has apex their product object and legs the two projections. It is a limit cone: a pair of maps into the two factors induces their pairing, the two projections of that pairing recover the given maps, and any map with those projections equals the pairing.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prod
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

open ApproximableMap

attribute [instance] instCategoryInfoSysObj

def productLimitCone (X Y : InfoSysObj.{u}) : LimitCone (pair X Y) where
  cone := BinaryFan.mk (P := InfoSysObj.prod X Y)
    (fstMap X.sys Y.sys) (sndMap X.sys Y.sys)
  isLimit := by
    refine BinaryFan.IsLimit.mk _
      (fun {T : InfoSysObj.{u}} (f : T ⟶ X) (g : T ⟶ Y) => pairMap X.sys Y.sys f g)
      ?_ ?_ ?_
    · intro T f g
      exact @comp_fstMap_pairMap X.Token Y.Token T.Token _ _ _
        X.sys Y.sys T.sys f g
    · intro T f g
      exact @comp_sndMap_pairMap X.Token Y.Token T.Token _ _ _
        X.sys Y.sys T.sys f g
    · intro T f g m hf hg
      exact @pairMap_unique X.Token Y.Token T.Token _ _ _
        X.sys Y.sys T.sys f g m hf hg

end InfoSys

end DomainTheory.InformationSystems
