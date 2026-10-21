/-ai
Equality of two enumerated sum neighbourhoods is recursively decidable.

The four comparisons of the two tags with zero and with one are recursively decidable, as are equality of the two first-presentation components and equality of the two second-presentation components. By the equality criterion for the enumeration, the predicate is the disjunction of both tags lying off zero and one, both tags zero with equal first components, and both tags one with equal second components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.recDec_setEq₀
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.recDec_setEq₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

include h₁ in
/-- **`sumEnum u.1 = sumEnum u.2` is recursively decidable** (the `of_iff` translation of
`sumEnum_eq_iff` into the tag/component deciders). -/
theorem eqSEdec :
    RecDecidable (fun u => sumEnum P₀ P₁ u.unpair.1 = sumEnum P₀ P₁ u.unpair.2) := by
  have hX0 : RecDecidable (fun u => u.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hX1 : RecDecidable (fun u => u.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hY0 : RecDecidable (fun u => u.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hY1 : RecDecidable (fun u => u.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hE0 : RecDecidable (fun u => P₀.X u.unpair.1.unpair.2 = P₀.X u.unpair.2.unpair.2) :=
    recDec_setEq₀ (Nat.Primrec.right.comp Nat.Primrec.left) (Nat.Primrec.right.comp Nat.Primrec.right)
  have hE1 : RecDecidable (fun u => P₁.X u.unpair.1.unpair.2 = P₁.X u.unpair.2.unpair.2) :=
    recDec_setEq₁ (Nat.Primrec.right.comp Nat.Primrec.left) (Nat.Primrec.right.comp Nat.Primrec.right)
  exact RecDecidable.of_iff (fun u => sumEnum_eq_iff (h₁ := h₁) u.unpair.1 u.unpair.2)
    (((hX0.not.and hX1.not).and (hY0.not.and hY1.not)).or
      (((hX0.and hY0).and hE0).or ((hX1.and hY1).and hE1)))

end Sum

end DomainTheory.NeighbourhoodSystems
