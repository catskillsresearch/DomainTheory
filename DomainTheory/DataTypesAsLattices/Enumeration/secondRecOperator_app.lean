/-ai
Applying the second recursion operator to an element u yields the second recursion value of u.

The combinator S(S(K S) K)(K C), where C is the substitution combinator, applied to u reduces by the three-place S equation, the two-place K equation, and the SK composition law to S(K u) C. Rewriting the operator by SK composition, that reduction, and the application law for the application combinator, the two sides have the same graph. At each numeral m, SK composition and the fact that C realizes the substitution m ↦ apply(m)(num(m)) identify the application with u at the numeral of that substitution, which is the graph of the second recursion value.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubstC_realizes

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem secondRecOperator_app (u : Pomega) :
    funOf secondRecOperator u = secondRecVal u := by
  have hsubst :
      (Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ Scomb) ⬝ Kcomb) ⬝ (Kcomb ⬝ secondRecSubstC)) ⬝ u =
        Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC := by
    rw [Scomb_beta3, Kcomb_beta2, SK_comp]
  rw [secondRecOperator, SK_comp, hsubst, dollarC_app]
  apply congrArg graph
  funext x
  have hreal (m : ℕ) :
      (Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC) ⬝ ofNat m =
        u ⬝ ofNat (secondRecSubst m) := by
    rw [SK_comp, secondRecSubstC_realizes]
  ext k
  simp [seqFun, hreal, secondRecSubst]

end DomainTheory.DataTypesAsLattices
