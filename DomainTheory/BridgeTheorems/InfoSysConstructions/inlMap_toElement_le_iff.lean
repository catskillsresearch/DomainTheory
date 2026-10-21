/-ai
The left image of an element x lies under the left image of an element y if and only if x lies under y.

If the images are ordered and a token belongs to x, the round trip through left-sum extraction puts the corresponding left token in the image of x, hence in the image of y, and transporting back through the extraction for y puts the token in y. The converse is monotonicity of the element map of the left inclusion.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.left_bot_mem_inlMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumElementLft_inlMap_toElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem inlMap_toElement_le_iff {x y : A.Element} :
    (inlMap A B).toElement x ≤ (inlMap A B).toElement y ↔ x ≤ y := by
  constructor
  · intro h a ha
    have : SumToken.left a ∈ ((inlMap A B).toElement x).carrier := by
      -- from sumElementLft_inl round-trip carrier
      have hx := sumElementLft_inlMap_toElement A B x
      -- a ∈ x = sumElementLft ⇒ left a ∈ inl x
      have : a ∈ (sumElementLft A B ((inlMap A B).toElement x) A.bot
          (left_bot_mem_inlMap_toElement A B x)).carrier := by
        simpa [hx] using ha
      exact this
    exact (sumElementLft_inlMap_toElement A B y) ▸
      (show a ∈ (sumElementLft A B ((inlMap A B).toElement y) A.bot
          (left_bot_mem_inlMap_toElement A B y)).carrier from h this)
  · exact (inlMap A B).toElement_mono

end InfoSysConstructions

end DomainTheory.BridgeTheorems
