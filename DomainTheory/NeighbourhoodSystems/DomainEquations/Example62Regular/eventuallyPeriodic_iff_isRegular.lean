/-ai
The language of a total tree is a regular event if and only if the tree is eventually periodic.

The left-quotient operation of the language equals the composite of the tree language with the subtree selector, by extensionality and the symmetric form of the subtree-quotient law. Regularity rewrites as finiteness of the range of left quotients. After substitution, that range is the image of the range of the selector, and finiteness of the image is equivalent to finiteness of the range because the tree language is injective there; the equivalence is reversed to match the stated order.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.treeLang_select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.treeLang_injective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}


/-- **Scott's closing claim, made precise (Example 6.2).** A tree's language `L_a` is a *regular
event* of automata theory **iff** the tree is eventually periodic. This is the Myhill–Nerode theorem
in disguise: the subtrees `aσ` are the left quotients `σ⁻¹ L_a` (`treeLang_select`), so "finitely many
subtrees" is "finitely many left quotients", which Myhill–Nerode equates with regularity. -/
theorem eventuallyPeriodic_iff_isRegular (a : Tree n) :
    EventuallyPeriodic a ↔ (treeLang a).IsRegular := by
  have hcomp : (treeLang a).leftQuotient = treeLang ∘ select a :=
    funext fun σ => (treeLang_select a σ).symm
  rw [Language.isRegular_iff_finite_range_leftQuotient, hcomp, Set.range_comp]
  exact (Set.finite_image_iff (treeLang_injective.injOn)).symm

end Example62Regular
end DomainTheory.NeighbourhoodSystems
