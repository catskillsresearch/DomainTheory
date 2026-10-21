/-ai
The binary sequence constructor of x and y equals the combinator S(S(K(cond x))(S(K(cond y zero)) pred)) I, where I is S K K.

The inner combinator S(K(cond(y)(zero))) pred is the graph of z ↦ cond(pred z, y, ⊥), by the two-place S equation, the two-place K equation, two uses of the predecessor equation, the definitional equality of zero with the numeral 0, equation 2.6, and the three-place conditional equation. Applying S(K(cond x)) to that combinator yields the graph of z ↦ cond(x) at cond(pred z, y, ⊥), by the two-place S equation, the previous identity, the two-place K equation, and the β-equation, using Scott continuity of the left conditional composed with continuity of predecessor. The outer S of this graph applied to S K K then reduces by the two-place S equation, that identity, and S K K = I. Pointwise, the identity graph acts as the identity by continuity of the identity, the remaining graph β-reduces by continuity of application of cond(x) composed with continuity of the left conditional of y and bottom composed with continuity of predecessor, and the three-place conditional equation is the binary sequence constructor.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- `seq2 x y` is the combinator `S (S (K (cond x)) (S (K (cond y ⊥)) pred)) I`. -/
theorem seq2_eq_SK (x y : Pomega) :
    seq2 x y =
      funOf (funOf Scomb
          (funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
            (funOf (funOf Scomb
                (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
              predC)))
        (funOf (funOf Scomb Kcomb) Kcomb) := by
  have hinter :
      funOf (funOf Scomb
          (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
        predC =
      graph (fun z => condSet (predSet z) y botElem) := by
    rw [Scomb_beta2]
    apply congrArg graph
    funext z
    rw [Kcomb_beta2, predC_app, predC_app]
    have : zeroC = ofNat 0 := rfl
    rw [this, eq_2_6, condC_beta3]
  have hF :
      funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
        (funOf (funOf Scomb
            (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
          predC) =
      graph (fun z =>
        funOf (funOf condC x) (condSet (predSet z) y botElem)) := by
    rw [Scomb_beta2, hinter]
    apply congrArg graph
    funext z
    rw [Kcomb_beta2]
    apply congrArg (funOf (funOf condC x))
    exact beta (theorem_1_3 (condSet_isScottContinuous_left y botElem)
      predSet_isScottContinuous) z
  rw [Scomb_beta2, hF, SKK_eq_I]
  apply congrArg graph
  funext z
  have hz : funOf (graph (fun x => x)) z = z := beta id_isScottContinuous z
  rw [hz]
  have hβ : funOf (graph (fun z =>
      funOf (funOf condC x) (condSet (predSet z) y botElem))) z =
      funOf (funOf condC x) (condSet (predSet z) y botElem) :=
    beta (theorem_1_3 (funOf_isScottContinuous (funOf condC x))
      (theorem_1_3 (condSet_isScottContinuous_left y botElem)
        predSet_isScottContinuous)) z
  rw [hβ, condC_beta3]

end DomainTheory.DataTypesAsLattices
