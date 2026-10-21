/-ai
The inverse of the product isomorphism sends a pair of an element a and a sequence b to the sequence that begins with a and then follows the components of b.

The forward isomorphism applied to that cons sequence returns the original pair: its component at zero is a and its tail is b, by the component formulas for cons and the reconstruction of a sequence from its components. Applying the inverse therefore returns the cons sequence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterProdIso_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The inverse iso is "cons".** `iterProdIso⁻¹ ⟨a, b⟩ = ⟨a, b₀, b₁, …⟩`. -/
theorem iterProdIso_symm_pair (a : V.Element) (b : (iterSys V).Element) :
    (iterProdIso V).symm (pair a b) = ofSeq (consSeq a b) := by
  have hkey : iterProdIso V (ofSeq (consSeq a b)) = pair a b := by
    rw [iterProdIso_apply]
    congr 1
    · rw [component_ofSeq, consSeq_zero]
    · have : (fun n => component (ofSeq (consSeq a b)) (n + 1)) = fun n => component b n := by
        funext n; rw [component_ofSeq, consSeq_succ]
      rw [this, ofSeq_component]
  rw [← hkey, OrderIso.symm_apply_apply]

end Exercise618

end DomainTheory.NeighbourhoodSystems
