/-ai
The right image of an element x lies under the right image of an element y if and only if x lies under y.

If the images are ordered and a token belongs to x, the round trip through right-sum extraction puts the corresponding right token in the image of x, hence in the image of y, and transporting back through the extraction for y puts the token in y. The converse is monotonicity of the element map of the right inclusion.
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
public import DomainTheory.BridgeTheorems.InfoSysConstructions.right_bot_mem_inrMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumElementRht_inrMap_toElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem inrMap_toElement_le_iff {x y : B.Element} :
    (inrMap A B).toElement x ≤ (inrMap A B).toElement y ↔ x ≤ y := by
  constructor
  · intro h b hb
    have : SumToken.right b ∈ ((inrMap A B).toElement x).carrier := by
      have hx := sumElementRht_inrMap_toElement A B x
      have : b ∈ (sumElementRht A B ((inrMap A B).toElement x) B.bot
          (right_bot_mem_inrMap_toElement A B x)).carrier := by
        simpa [hx] using hb
      exact this
    exact (sumElementRht_inrMap_toElement A B y) ▸
      (show b ∈ (sumElementRht A B ((inrMap A B).toElement y) B.bot
          (right_bot_mem_inrMap_toElement A B y)).carrier from h this)
  · exact (inrMap A B).toElement_mono

end InfoSysConstructions

end DomainTheory.BridgeTheorems
